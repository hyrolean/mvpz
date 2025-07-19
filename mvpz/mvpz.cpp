// mvpz.cpp : コンソール アプリケーションのエントリ ポイントを定義します。
//

#include "stdafx.h"
#include <iterator>
#include <memory>
#include <string>
#include <vector>
#include <deque>
#include <set>
#include <cstring>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <process.h>
#include <tlhelp32.h>
#include <MMSYSTEM.h>
#include <shlobj.h>
#pragma comment(lib, "WinMM.lib")

using namespace std;

//#<OFF>#define EQUALITY_CHECK_ATTRIBUTES

//---------------------------------------------------------------------------
// forward declarations

void help() ;
void perrorf(const char *format, ...) ;
void statusf(const char *format, ...) ;
void __inline clrstatus() { statusf(" "); }
bool equality(string fileDest, const WIN32_FIND_DATAA &dataSrc) ;
bool transfer(string inputFile, string outputFile, const WIN32_FIND_DATAA &data) ;

//---------------------------------------------------------------------------

  // CACHE

struct CACHEDATA {
  CACHEDATA(size_t size_=0,void *data_=0) { init(size_,data_); }
  CACHEDATA(const CACHEDATA &src) {
    ref = src.ref ;
    ref->incRef() ;
  }
  ~CACHEDATA() {
    if(!ref->decRef()) {
      if(ref->data) free(ref->data) ;
      delete ref ;
    }
  }
  CACHEDATA &operator =(const CACHEDATA &src) {
    if(src.ref!=this->ref) {
      if(!ref->decRef()) {
        if(ref->data) free(ref->data) ;
        delete ref ;
      }
      ref = src.ref ;
      ref->incRef() ;
    }
    return *this ;
  }
  void *data(size_t offset=0) const { return &((char*)ref->data)[offset] ; }
  size_t size() const { return ref->size ; }
  void resize(size_t size_) {
    exclusive_lock lock(&ref->excl) ;
    if(size_>ref->alloc_size) {
      if(!ref->data)
        ref->data=malloc(size_) ;
      else
        ref->data=realloc(ref->data,size_) ;
      ref->alloc_size = size_ ;
    }
    ref->size = size_ ;
  }
private:
  struct ref_t {
    exclusive_object excl ;
    void *data ;
    size_t size ;
    size_t alloc_size ;
    ref_t() {
      refCnt=1;
    }
    int incRef() {
      exclusive_lock lock(&excl) ;
      return ++refCnt ;
    }
    int decRef() {
      exclusive_lock lock(&excl) ;
      return --refCnt ;
    }
  private:
    int refCnt ;
  } *ref ;
  void init(size_t size_,void *data_) {
    ref = new ref_t ;
    if(size_) {
      ref->data = malloc(size_) ;
      ref->size = size_ ;
      if(data_) memcpy(ref->data,data_,size_) ;
    }else {
      ref->data = 0 ;
      ref->size = 0 ;
    }
    ref->alloc_size = size_ ;
  }
};
typedef std::deque<CACHEDATA> CACHE ;

struct LINECACHE {
  bool circular_offline;
  LINECACHE(size_t num_,size_t size_=0) {
    circular_offline=false ;
    for(size_t i=0;i<num_;i++) {
      CACHEDATA data(size_);
      offline.push_back(data) ;
    }
  }
  size_t num_offline() const { return offline.size() ; }
  size_t num_online() const { return online.size() ; }
  CACHEDATA pop_offline() {
    exclusive_lock lock(&excl) ;
    if(circular_offline) {
      CACHEDATA data = offline.front() ;
      offline.pop_front() ;
      return data ;
    }
    CACHEDATA data = offline.back() ;
    offline.pop_back() ;
    return data ;
  }
  void push_offline(const CACHEDATA data) {
    exclusive_lock lock(&excl) ;
    offline.push_back(data) ;
  }
  void push_offline_cache(const CACHE &cache) {
    exclusive_lock lock(&excl) ;
    copy(cache.begin(),cache.end(),back_inserter(offline)) ;
  }
  CACHEDATA pop_online() {
    exclusive_lock lock(&excl) ;
    CACHEDATA data = online.front() ;
    online.pop_front() ;
    return data ;
  }
  void push_online(const CACHEDATA data) {
    exclusive_lock lock(&excl) ;
    online.push_back(data) ;
  }
  void push_online_cache(const CACHE &cache) {
    exclusive_lock lock(&excl) ;
    copy(cache.begin(),cache.end(),back_inserter(online)) ;
  }
private:
  exclusive_object excl ;
  CACHE offline ;
  CACHE online ;
};

//---------------------------------------------------------------------------
// variables

set<string> pauseExes ;
DWORD dataPacket = 12000 ; // Nearly ethernet MTU (1500) x 8
bool verbose = false ;
double dataRate = 1.f ;
__int64 necessaryFreeSpace = 0 ;
bool forceMoveAllFiles = false ;
bool priorFreeSpace = false ;
bool removeSourceFiles = true ;
bool overwriteDestFiles = false ;
bool moveRecursively = false ;
bool USEMMTIMER = false ;
bool PREVENTSUSPENDING = false ;
DWORD SLEEP_DELAY = 30 ;

LINECACHE *lineCache ;
DWORD maxCache = 128 ;
HANDLE readEvent,wroteEvent ;
const DWORD THREADWAIT = 1000 ;
const DWORD WAITTHREAD_TIMEOUT = 30000 ;
const DWORD MAXAVG = 25 ;

//---------------------------------------------------------------------------
static string unc_root_of(string filename)
{
  string root = file_drive_of(filename);
  if(root.empty()) {
    wstring wfname = mbcs2wcs(filename) ;
    if(wfname.length()>=2) {
      if(wfname[0]==L'\\'&&wfname[1]==L'\\') do {
        size_t i;
        for(i=2;i<wfname.length()&&wfname[i]==L'\\';i++);
        if(i>=wfname.length()) break;
        for(;i<wfname.length();i++) {
          if(wfname[i]==L'\\') break;
        }
        for(i++;i<wfname.length()&&wfname[i]==L'\\';i++);
        if(i>=wfname.length()) break;
        size_t j=i;
        for(;i<wfname.length();i++) {
          if(wfname[i]==L'\\') break;
        }
        if(i==j) break;
        root = wcs2mbcs(wfname.substr(0,i)) ; // \\server\place
      }while(0);
    }
  }
  return root;
}
//---------------------------------------------------------------------------
static __int64 GetDiskFreeSpaceFromFileName(string FileName, __int64 *pAlign = 0)
{
  string Drive = unc_root_of(FileName);

  DWORD SectorsPerCluster;
  DWORD BytesPerSector;
  DWORD FreeClusters;
  DWORD Clusters;

  BOOL Result=GetDiskFreeSpaceA(
    Drive.c_str(),
    &SectorsPerCluster,
    &BytesPerSector,
    &FreeClusters,
    &Clusters
  );

  if(Result) {
    if(pAlign) {
      *pAlign = __int64(SectorsPerCluster) * __int64(BytesPerSector) ;
    }
    return __int64(FreeClusters)*
           __int64(SectorsPerCluster)*
           __int64(BytesPerSector)       ;
  }

  return -1;
}
//---------------------------------------------------------------------------
static string IntToKMGT(__int64 val)
{
  double bytes=(double)val;
  bool neg = bytes<0 ;
  if(neg) bytes = -bytes ;
  int unitno=-1;
  while(bytes>1024) {
    bytes/=1024; unitno++;
  }
  string text;
  if(unitno<0)
    text = itos((int)val);
  else
    text = str_printf("%5.2f",bytes);
  if(unitno>=0) {
    switch(unitno) {
      case 0: text=text+"K"; break;
      case 1: text=text+"M"; break;
      case 2: text=text+"G"; break;
      case 3: text=text+"T"; break;
      default: text=text+"?"; break;
    }
  }
  return (neg?"-":"")+text;
}
//---------------------------------------------------------------------------
static bool IsDirectory(string Path)
{
  return
    unc_root_of(Path)==Path ||
    folder_is_existed(Path) ;
}
//---------------------------------------------------------------------------
static bool IsDrive(string Path)
{
  return file_drive_of(Path)==Path;
}
//---------------------------------------------------------------------------
static bool __fastcall SetFileNameTime(string FileName,
  const FILETIME *lpftCreation, const FILETIME *lpftLastAccess,
  const FILETIME *lpftLastWrite)
{
  HANDLE hFile =
    CreateFileA(
      FileName.c_str(),
      GENERIC_READ|GENERIC_WRITE,
      FILE_SHARE_READ|FILE_SHARE_WRITE,
      0, OPEN_EXISTING, 0, 0 );
  if(!hFile) return false;
  BOOL RESULT = SetFileTime(hFile,lpftCreation,lpftLastAccess,lpftLastWrite);
  CloseHandle(hFile);
  return RESULT?true:false;
}
//---------------------------------------------------------------------------

    class suspend_preventer {
        void PreventSuspending(BOOL bInner) {
            if(bInner) {
                SetThreadExecutionState(
                    ES_CONTINUOUS|ES_SYSTEM_REQUIRED|ES_AWAYMODE_REQUIRED);
            }else {
                SetThreadExecutionState(ES_CONTINUOUS);
            }
        }
    public:
        suspend_preventer(bool doPrevent_) : doPrevent(doPrevent_) {
            if(doPrevent) PreventSuspending(TRUE);
        }
        ~suspend_preventer() {
            if(doPrevent) PreventSuspending(FALSE);
        }
    private:
        bool doPrevent ;
    };

    struct transport_file {
      string file ;
      string relative ;
      WIN32_FIND_DATAA data;
      transport_file(string file_, const WIN32_FIND_DATAA &data_, string relative_="")
       : file(file_), relative(relative_) {
        CopyMemory(&data,&data_,sizeof data);
      }
      transport_file(const transport_file &src)
       : file(src.file), relative(src.relative) {
        CopyMemory(&data,&src.data,sizeof data);
      }
      __int64 alignBytes(__int64 align) const {
        __int64 fileSz = __int64(data.nFileSizeHigh)<<32 | __int64(data.nFileSizeLow) ;
        if(!fileSz) return 0;
        return (fileSz + align - 1) & ~(align-1) ;
      }
      bool operator <(const transport_file &rhs) const {
        __int64 ltm = __int64(data.ftLastWriteTime.dwHighDateTime)<<32 | __int64(data.ftLastWriteTime.dwLowDateTime) ;
        __int64 rtm = __int64(rhs.data.ftLastWriteTime.dwHighDateTime)<<32 | __int64(rhs.data.ftLastWriteTime.dwLowDateTime) ;
        return ltm < rtm ;
      }
    };

    template<typename Container> __int64 CalcAlignBytes(const Container &files, __int64 align) {
      __int64 total = 0 ;
      for(Container::const_iterator pos=files.begin(); pos!= files.end(); ++pos)
        total += pos->alignBytes(align) ;
      return total ;
    }

    struct auto_handle {
      HANDLE handle;
      auto_handle(HANDLE handle_): handle(handle_) {}
      ~auto_handle() { if(handle!=INVALID_HANDLE_VALUE) CloseHandle(handle); }
    };

int _tmain(int argc, _TCHAR* argv[])
{
  string exeFileName = wcs2mbcs(argv[0]) ;
  vector<string> files ;

  int error_level = 1 ;

  int argi;
  for(argi=1;argi<argc;argi++) {
    _TCHAR *arg = argv[argi];
    if(arg[0]!=L'/') {
      files.push_back(wcs2mbcs(arg)) ;
      continue ;
    }
    for(_TCHAR *param = &arg[1] ; *param ; param++) {
      switch(*param) {
        case L'd': // data packet size
          if(argi+1>=argc) {
            help() ;
            perrorf("Argument vector overflow.") ;
            return error_level ;
          }
          dataPacket = acalci(wcs2mbcs(argv[++argi]).c_str()) ;
          break ;
        case L'c': // max cache
          if(argi+1>=argc) {
            help() ;
            perrorf("Argument vector overflow.") ;
            return error_level ;
          }
          maxCache = acalci(wcs2mbcs(argv[++argi]).c_str()) ;
          break ;
        case L'a': // adjust disk free space
          if(argi+1>=argc) {
            help() ;
            perrorf("Argument vector overflow.") ;
            return error_level ;
          }
          necessaryFreeSpace = acalci64(wcs2mbcs(argv[++argi]).c_str()) ;
          break ;
        case L'w': // pause executable (enable exe wait mode)
          if(argi+1>=argc) {
            help() ;
            perrorf("Argument vector overflow.") ;
            return error_level ;
          }
          {
            vector<string> exes;
            split(exes,upper_case(wcs2mbcs(argv[++argi])),';') ;
            copy(exes.begin(),exes.end(),inserter(pauseExes,pauseExes.begin())) ;
          }
          break ;
        case L't': // traffic data rate
          if(argi+1>=argc) {
            help() ;
            perrorf("Argument vector overflow.") ;
            return error_level ;
          }
          dataRate = atof(wcs2mbcs(argv[++argi]).c_str()) ;
          break;
        case L's': // sleep delay
          if(argi+1>=argc) {
            help() ;
            perrorf("Argument vector overflow.") ;
            return error_level ;
          }
          SLEEP_DELAY = acalci(wcs2mbcs(argv[++argi]).c_str()) ;
          break ;
        case L'e': // precedence empty spaces
          priorFreeSpace = true;
          break;
        case L'f': // force moving mode
          forceMoveAllFiles = true ;
          break;
        case L'n': // not remove source files
          removeSourceFiles = false ;
          break;
        case L'o': // overwrite dest files
          overwriteDestFiles = true ;
          break;
        case L'r': // move directories recursively
          moveRecursively = true ;
          break;
        case L'M': // enable multi media timer
          USEMMTIMER = true;
          break;
        case L'P': // prevent suspending
          PREVENTSUSPENDING = true ;
          break;
        case L'v': // verbose
          verbose = true ;
          break ;
        case L'h': // help
          help() ;
          return 0 ;
          break ;
        default:
          help() ;
          perrorf("Unknown option: `%c'.",*param) ;
          return error_level ;
      }
    }
  }

  error_level++; // 2

  if(!files.size()) {
    perrorf("No source file.") ;
    return error_level ;
  }

  error_level++; // 3

  if(files.size()==1) {
    perrorf("No destination file.") ;
    return error_level ;
  }

  string outputFile = files.back() ;
  files.pop_back() ;

  // enumerate files
  vector<transport_file> transportFiles ;
  vector<string> sourceDirs ;
  __int64 totalBytes = 0 ;
  if(verbose) statusf("Enumerating source files...");
  for(size_t i=0;i<files.size();i++) {
    string dir = "" ;
    deque<string> dirs ;
    do {
      string inputFile = files[i] ;
      if(!dirs.empty()) {
        dir = dirs.front() ; dirs.pop_front();
        string inputDir = file_path_of(inputFile) + dir ;
        inputFile = inputDir + "\\*.*" ;
        sourceDirs.push_back(inputDir);
      }
      WIN32_FIND_DATAA data;
      HANDLE hFind = FindFirstFileA(inputFile.c_str(),&data);
      if(hFind!=INVALID_HANDLE_VALUE) {
          do {
              if(data.dwFileAttributes&FILE_ATTRIBUTE_DIRECTORY) {
                if(moveRecursively) {
                  string dirnam = data.cFileName ;
                  if(dirnam!="."&&dirnam!="..") {
                    string dirpath = dir==""?dirnam:dir+"\\"+dirnam ;
                    dirs.push_back(dirpath);
                  }
                }
                continue ;
              }
              if(!forceMoveAllFiles&&(data.dwFileAttributes&(FILE_ATTRIBUTE_READONLY|FILE_ATTRIBUTE_HIDDEN|FILE_ATTRIBUTE_SYSTEM))) continue ;
              string filenam = data.cFileName ;
              string input = file_path_of(inputFile)+filenam ;
              transportFiles.push_back(transport_file(input,data,dir==""?filenam:dir+"\\"+filenam));
              totalBytes += __int64(data.nFileSizeHigh)<<32 | __int64(data.nFileSizeLow) ;
          }while(FindNextFileA(hFind,&data)) ;
          FindClose(hFind) ;
      }
    }while(!dirs.empty());
  }
  if(verbose) clrstatus();

  if(!transportFiles.size()) {
    printf("No source file be found.\n") ;
    return 0 ;
  }

  sort(transportFiles.begin(),transportFiles.end());

  if(verbose) {
    int n = (int) transportFiles.size();
    if(n==1)
      printf("1 source file (%s bytes %s be estimated)\n",
        IntToKMGT(totalBytes).c_str(),removeSourceFiles?"moving":"coping");
    else
      printf("Total %d source files (%s bytes %s be estimated)\n",
        n, IntToKMGT(totalBytes).c_str(),removeSourceFiles?"moving":"coping");
  }

  error_level++; // 4

  // choose destination
  vector<string> outputCandidates;
  split(outputCandidates,outputFile,';');
  __int64 totalAlignBytes = 0 ;
  if(outputCandidates.size()>=2) {
    int candidate=-1;
    __int64 maxFreeSpace=-1;
    for(size_t i=0;i<outputCandidates.size();i++) {
      string outDir = outputCandidates[i] ;
      if(!IsDirectory(outDir)) {
        perrorf("Dest must be directory path because of multi dest candidates. (%s)",outDir.c_str()) ;
        return error_level ;
      }
      __int64 align = 0 ;
      __int64 space = GetDiskFreeSpaceFromFileName(outDir, &align) - necessaryFreeSpace ;
      __int64 alignBytes = CalcAlignBytes(transportFiles, align) ;
      if(space-alignBytes>maxFreeSpace) {
        maxFreeSpace = space-alignBytes ;
        candidate = (int) i ;
        totalAlignBytes = alignBytes;
        if(!priorFreeSpace&&totalAlignBytes<=space)
          break;
      }
    }
    if(candidate<0) {
      perrorf("No free destination space." ) ;
      return error_level;
    }
    outputFile = outputCandidates[candidate];
    if(verbose)
      printf("Destination is decided to \"%s\" from multi candidates. (%s bytes free)\n"
        ,outputFile.c_str(), IntToKMGT(maxFreeSpace+totalAlignBytes).c_str()) ;
  }

  error_level++; // 5

  if(files.size()>=2&&!IsDirectory(outputFile)) {
    perrorf("Destination must be directory path because of multi target source files.") ;
    return error_level ;
  }

  error_level++; // 6

  __int64 destAlign = 0 ;
  __int64 destFreeSpace = GetDiskFreeSpaceFromFileName(outputFile, &destAlign) ;
  if(totalAlignBytes==0)
    totalAlignBytes = CalcAlignBytes(transportFiles, destAlign) ;
  if(destFreeSpace<totalAlignBytes) {
    __int64 needSize = totalAlignBytes - destFreeSpace ;
    perrorf("No free destination space (%s[%lld] bytes more free space needed).",
      IntToKMGT(needSize).c_str(), needSize ) ;
    return error_level ;
  }

  auto_handle aReadEvent( readEvent = CreateEvent(0,FALSE,FALSE,0) );
  auto_handle aWroteEvent( wroteEvent = CreateEvent(0,FALSE,FALSE,0) );

  LINECACHE aLCache(maxCache);
  lineCache = &aLCache;

  suspend_preventer suspendPreventer(PREVENTSUSPENDING);

  error_level++ ; // 7

  // transfer files
  for(size_t i=0;i<transportFiles.size();i++) {
    string output = outputFile ;
    if(IsDirectory(output)) {
      if(!IsDrive(output)) output += "\\";
      output += transportFiles[i].relative;
      // force create directories to file_path_of(output)
      if(moveRecursively)
        SHCreateDirectoryExA(NULL,file_path_of(output).c_str(),NULL);
    }
    if(!overwriteDestFiles&&file_is_existed(output)) {
      if(equality(output,transportFiles[i].data)) {
        printf("File `%s' is skipped due to already be existing.\n",transportFiles[i].data.cFileName) ;
        continue ;
      }
    }
    if( !transfer(
          transportFiles[i].file, output,
          transportFiles[i].data ) ) {
      perrorf("Aborted.") ;
      return error_level ;
    }
  }

  error_level++ ; // 8

  string action = "moved" ;

  // remove files
  if(removeSourceFiles) {
    if(verbose) statusf("Removing source files...");
    for(size_t i=0;i<transportFiles.size();i++) {
      const string &file = transportFiles[i].file;
      if(forceMoveAllFiles)
        SetFileAttributesA(file.c_str(),FILE_ATTRIBUTE_NORMAL);
      if(!DeleteFileA(file.c_str())) {
        clrstatus();
        perrorf("Input file `%s' removing failed.",file.c_str()) ;
        return error_level ;
      }
    }
    // remove all empty directories if files are moved recursively
    if(moveRecursively) {
      if(verbose) statusf("Removing source directories...");
      sort(sourceDirs.rbegin(),sourceDirs.rend());
      for(size_t i=0;i<sourceDirs.size();i++) {
        RemoveDirectoryA(sourceDirs[i].c_str());
      }
    }
    if(verbose) clrstatus();
  }else {
    action = "copied";
  }

  int n = (int) transportFiles.size() ;
  if(!n)
    printf("No file %s.\n",action.c_str()) ;
  else if(n==1)
    printf("1 file %s.\n",action.c_str()) ;
  else
    printf("Total %d files %s.\n",n,action.c_str()) ;

  return 0;
}

//---------------------------------------------------------------------------
void help()
{
  printf("MoVe files with PauZing.\n\n") ;
  printf("usage: mvpz [options] source [source2[ ...]] dest[;dest2[;...]]\n\n") ;
  printf("options:\n") ;
  printf("\t/d data_size\t... Set trasfering packet size ( bytes [current=%d] ).\n",dataPacket) ;
  printf("\t/c max_cache\t... Set trasfering maximum cache ( packets [current=%d] ).\n",maxCache) ;
  printf("\t/a free_space\t... Adjust dest disk free space ( e.g. 10M=10MiBytes, 5G=5GiBytes ).\n");
  printf("\t/w pause_exe\t... Wait trasmitting while pause_exe is executing.\n") ;
  printf("\t/t data_rate\t... Set traffic data rate ( e.g. 1=100%%[default], 0.75=75%%, 0.5=50%% ).\n");
  printf("\t/s sleep_delay\t... Set sleeping duration per 1 traffic stall ( msec [current=%d] ).\n",SLEEP_DELAY);
  printf("\t/e\t\t... Prioritize disk free space of multi dest candidates.\n") ;
  printf("\t/f\t\t... Force move read-only, hidden and system files.\n");
  printf("\t/n\t\t... Do not remove source files.\n");
  printf("\t/o\t\t... Overwrite existing dest files.\n");
  printf("\t/r\t\t... Move directories recursively.\n");
  printf("\t/M\t\t... Use multimedia timer on interrupt.\n");
  printf("\t/P\t\t... Prevent suspending on trasmitting files.\n");
  printf("\t/v\t\t... Verbose proceedings.\n") ;
  printf("\t/h\t\t... Show this help.\n\n") ;
}
//---------------------------------------------------------------------------
void perrorf(const char *format, ...)
{
  va_list marker ;
  va_start( marker, format ) ;
  int edit_ln = _vscprintf(format, marker);
  if(edit_ln++>0) {
      char *edit_str = static_cast<char*>(alloca(edit_ln)) ;
      vsprintf_s( edit_str, edit_ln, format, marker ) ;
      fputs( "ERROR: ", stderr );
      fputs( edit_str, stderr );
      fputc( '\n', stderr ) ;
  }
  va_end( marker ) ;
}
//---------------------------------------------------------------------------
void statusf(const char *format, ...)
{
  va_list marker ;
  va_start( marker, format ) ;
  int edit_ln = _vscprintf(format, marker);
  if(edit_ln++>0) {
      edit_ln = max<int>(edit_ln,80);
      char *edit_str = static_cast<char*>(alloca(edit_ln)) ;
      vsprintf_s( edit_str, edit_ln, format, marker ) ;
      size_t ln = strlen(edit_str) ;
      if(ln<=78) {
        for(size_t i=ln;i<=77;i++) {
          edit_str[i] = 0x20 ;
        }
        edit_str[78] = '\r' ;
        edit_str[79] = '\0' ;
      }
      fputs( edit_str, stderr );
  }
  va_end( marker ) ;
}
//---------------------------------------------------------------------------
bool pause_status(string *pCausingFileName=0)
{
  bool Result = false ;
  HANDLE Process = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0) ;

  PROCESSENTRY32 Entry ;
  ZeroMemory(&Entry,sizeof(Entry)) ;
  Entry.dwSize = sizeof(Entry) ;

  if(Process32First(Process,&Entry)) {
    do {

      string FileName = upper_case(wcs2mbcs(Entry.szExeFile)) ;
      if(pauseExes.find(FileName)!=pauseExes.end()) {
        if(pCausingFileName) *pCausingFileName = FileName ;
        Result = true ; break ;
      }

    } while(Process32Next(Process,&Entry)) ;
  }

  CloseHandle(Process) ;

  return Result ;
}
//---------------------------------------------------------------------------
bool terminated = false ;

    class mm_interval_lock {
        static int refCnt;
        DWORD period_;
    public:
        mm_interval_lock(DWORD period) : period_(period) {
            if(USEMMTIMER&&!refCnt) timeBeginPeriod(period_);
            refCnt++;
        }
        ~mm_interval_lock() {
            --refCnt;
            if(USEMMTIMER&&!refCnt) timeEndPeriod(period_);
        }
    };
    int mm_interval_lock::refCnt=0;
    #define MMINTERVAL_PERIOD 10

    DWORD timeTick() {
      return USEMMTIMER ? timeGetTime() : GetTickCount() ;
    }

unsigned int __stdcall write_thread_proc (PVOID pv)
{
  {
    mm_interval_lock interlock(MMINTERVAL_PERIOD);
    HANDLE ost = *(HANDLE*)pv ;
    double trafficDrain = 0.0 ;
    if(dataRate>0.0&&dataRate<1.0) trafficDrain = 1.0/dataRate-1.0 ;
    for(;;) {
      DWORD ret = WaitForSingleObject(readEvent,THREADWAIT) ;
      if(terminated) break ;
      if(ret==WAIT_OBJECT_0) {
        DWORD start_tick = timeTick(), delta = 0;
        size_t remain ;
        do {
          if(!lineCache->num_online())
            break;
          CACHEDATA cache_data = lineCache->pop_online() ;
          remain = lineCache->num_online() ;
          if(cache_data.size()>0) {
            BYTE *data=static_cast<BYTE*>(cache_data.data()) ;
            DWORD len= (DWORD) cache_data.size();
            while(len>0) {
              DWORD wSize = 0 ;
              BOOL bWrite = WriteFile(ost, data, len, &wSize, 0) ;
              if(!bWrite) {
                perrorf("Write error occured.") ;
                terminated=true ;
                _endthreadex(1) ;
                return 1 ;
              }
              else data += wSize , len -= wSize ;
            }
          }
          lineCache->push_offline(cache_data);
          SetEvent(wroteEvent);
          if(trafficDrain>0.f) {
            DWORD end_tick = timeTick() ;
            DWORD duration ;
            if(end_tick>=start_tick) duration = end_tick-start_tick ;
            else duration = MAXDWORD - start_tick + end_tick+1 ;
            DWORD wait = DWORD( double(duration) * trafficDrain ) ;
            if(wait>=SLEEP_DELAY) {
              //printf("Sleep = %d \n",wait) ;
              Sleep(wait) ;
              start_tick = timeTick() ; //end_tick+wait ;
              #if 1
              if(start_tick>end_tick+wait)
                delta = start_tick-(end_tick+wait) ;
              else
              #endif
                delta = 0;
            }
          }
        }while(remain) ;
      }
    }
    terminated=true ;
  }
  _endthreadex(0) ;
  return 0 ;
}
//---------------------------------------------------------------------------
bool equality(string fileDest, const WIN32_FIND_DATAA &dataSrc)
{
  bool res = false ;

  WIN32_FIND_DATAA dataDest;
  HANDLE hFind = FindFirstFileA(fileDest.c_str(),&dataDest);
  if(hFind!=INVALID_HANDLE_VALUE) {
    if(dataSrc.nFileSizeHigh==dataDest.nFileSizeHigh&&
       dataSrc.nFileSizeLow==dataDest.nFileSizeLow) { // file size equality
      #ifdef EQUALITY_CHECK_ATTRIBUTES
      const DWORD modAttr = FILE_ATTRIBUTE_READONLY | FILE_ATTRIBUTE_HIDDEN | FILE_ATTRIBUTE_SYSTEM | FILE_ATTRIBUTE_ARCHIVE ;
      if(!((dataSrc.dwFileAttributes^dataDest.dwFileAttributes)&modAttr)) // same file attributes
      #endif
      {
        const __int64 msec = 10 ;  // 100ns x 10
        __int64 srcUpTime = __int64(dataSrc.ftLastWriteTime.dwHighDateTime)<<32 | __int64(dataSrc.ftLastWriteTime.dwLowDateTime) ;
        __int64 destUpTime = __int64(dataDest.ftLastWriteTime.dwHighDateTime)<<32 | __int64(dataDest.ftLastWriteTime.dwLowDateTime) ;
        __int64 delta = destUpTime - srcUpTime ;
        if(delta<0) delta = -delta ;
        if( delta <= 3000 * msec ) // update time within 3 seconds ( taking into consider the FAT32 file system )
          res = true ;
      }
    }
    FindClose(hFind) ;
  }

  return res ;
}
//---------------------------------------------------------------------------
bool transfer(string inputFile, string outputFile, const WIN32_FIND_DATAA &data)
{
  bool Result = true ;
  const FILETIME &ftCreation = data.ftCreationTime ;
  const FILETIME &ftLastAccess = data.ftLastAccessTime ;
  const FILETIME &ftLastWrite = data.ftLastWriteTime ;
  DWORD per = 0 ;
  DWORD tick = GetTickCount() ;
  __int64 fSize = __int64(data.nFileSizeHigh)<<32 | __int64(data.nFileSizeLow) ;
  __int64 wSize = 0, oSize = 0 ;
  deque<DWORD> avg;
  DWORD sumAvg = 0;
  do {
    HANDLE ist, ost, hThWrite;
    string fileName = file_name_of(inputFile) ;
    if(verbose) {
      printf("File `%s' is transferring...\n",fileName.c_str()) ;
    }
    auto_handle aIst(
      ist = CreateFileA(inputFile.c_str(), GENERIC_READ, FILE_SHARE_READ,
        0, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, 0) );
    if(ist==INVALID_HANDLE_VALUE) {
      perrorf("Could not open input file `%s'.",inputFile.c_str()) ;
      Result = false ;
      break ;
    }
    auto_handle aOst(
      ost = CreateFileA(outputFile.c_str(), GENERIC_WRITE, FILE_SHARE_READ,
        0, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, 0) );
    if(ost==INVALID_HANDLE_VALUE) {
      perrorf("Could not create output file `%s'.",outputFile.c_str()) ;
      Result = false ;
      break ;
    }
    terminated = false ;
    ResetEvent(readEvent) ;
    ResetEvent(wroteEvent) ;
    auto_handle aHThWrite(
      hThWrite = (HANDLE)_beginthreadex(0, 0, write_thread_proc, &ost,
        CREATE_SUSPENDED, 0) );
    if(hThWrite==INVALID_HANDLE_VALUE) {
      perrorf("Could not create writing file thread.") ;
      Result = false ;
      break ;
    }
    ResumeThread(hThWrite) ;
    string causingExe;
    while(wSize<fSize) {
      DWORD newTick = GetTickCount() ;
      if(newTick-tick>=THREADWAIT) {
        if(verbose) {
            if(avg.size()>=MAXAVG) {
              sumAvg -= avg.back();
              avg.pop_back();
            }
            DWORD rate = static_cast<DWORD>((wSize-oSize)*1000/(newTick-tick));
            sumAvg += rate;
            avg.push_front(rate);
            oSize = wSize;
        }
        tick = newTick ;
        if(pause_status(&causingExe)) {
          if(verbose)
            statusf("Transferring is paused (\"%s\" is up) %d%%...",causingExe.c_str(),per) ;
          else
            statusf("Transferring is paused...") ;
          do {
            Sleep(THREADWAIT) ;
          }while(pause_status()) ;
          clrstatus() ;
        }
        if(verbose&&fSize>0) {
          DWORD per = DWORD(wSize*100/fSize) ;
          DWORD rate = sumAvg / DWORD(avg.size()) ;
          statusf(" %d%% transferring completed...[%sB/s] ( %lld/ %lld)",
            per,IntToKMGT(rate).c_str(),wSize,fSize) ;
        }
      }
      if(terminated) break ;
      if(!lineCache->num_offline()) {
        WaitForSingleObject(wroteEvent,THREADWAIT) ;
        if(!lineCache->num_offline()) continue;
      }
      CACHEDATA cache_data = lineCache->pop_offline();
      cache_data.resize(dataPacket);
      DWORD n=0;
      if(!ReadFile(ist, cache_data.data(), dataPacket, &n, 0)||!n) {
        perrorf("Failed to reading file.") ;
        Result = false ;
        break ;
      }
      //n = min<DWORD>(n,DWORD(fSize-wSize)) ;
      if(n>0) {
        cache_data.resize(n);
        lineCache->push_online(cache_data);
        SetEvent(readEvent) ;
        wSize+=__int64(n) ;
      }else
        lineCache->push_offline(cache_data);
    }
    if(!terminated) {
      size_t remain ;
      do {
        remain = lineCache->num_online() ;
        if(remain)
          WaitForSingleObject(wroteEvent,THREADWAIT) ;
      }while(remain&&!terminated) ;
      if(terminated)
        Result=false ;
      else {
        terminated = true ;
        SetEvent(readEvent) ;
      }
    }else
      Result = false ;
    if(WaitForSingleObject(hThWrite,WAITTHREAD_TIMEOUT)!=WAIT_OBJECT_0) {
      TerminateThread(hThWrite,0) ;
      Result = false ;
    }else {
      DWORD bThRes=1;
      if(GetExitCodeThread(hThWrite,&bThRes)) {
        Result = bThRes == 0 ;
      }else Result = false;
    }
    if(verbose) {
      clrstatus() ;
      if(Result)
        printf("File `%s' (%lld bytes) transferring succeeded.\n",fileName.c_str(),wSize) ;
      else
        printf("File `%s' transferring failed.\n",fileName.c_str()) ;
    }
  }while(0) ;
  clrstatus() ;
  if(Result) do {
    if(!SetFileNameTime(outputFile,&ftCreation,&ftLastAccess,&ftLastWrite)) {
      perrorf("Output file `%s' time-stamp setting error.",outputFile.c_str()) ;
      Result = false ;
      break;
    }
    DWORD attr = GetFileAttributesA(inputFile.c_str());
    if(attr==INVALID_FILE_ATTRIBUTES) attr = 0 ;
    const DWORD modAttr = FILE_ATTRIBUTE_READONLY | FILE_ATTRIBUTE_HIDDEN | FILE_ATTRIBUTE_SYSTEM | FILE_ATTRIBUTE_ARCHIVE ;
    attr &= ~modAttr ;
    attr |= data.dwFileAttributes & modAttr ;
    if(!SetFileAttributesA(outputFile.c_str(),attr)) {
      perrorf("Output file `%s' attributes setting error.",outputFile.c_str()) ;
      Result = false ;
      break;
    }
  }while(0);
  return Result ;
}
//---------------------------------------------------------------------------
