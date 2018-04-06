#include <cstdio>
#include <memory>
#include <sstream>
#include <string>
#include <vector>
#include <iostream>
#include <fstream>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Basic/TargetOptions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Parse/ParseAST.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Rewrite/Frontend/Rewriters.h"
#include "clang/CodeGen/CodeGenAction.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Module.h"
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/Support/raw_os_ostream.h>

#if LLVM_VERSION_MAJOR >= 4 || (LLVM_VERSION_MAJOR == 3 && LLVM_VERSION_MINOR >= 5)
#include "llvm/IR/InstIterator.h"
#else
#include "llvm/Support/InstIterator.h"
#endif

#if LLVM_VERSION_MAJOR >= 4
#include <llvm/Bitcode/BitcodeWriter.h>
#else
#include <llvm/Bitcode/ReaderWriter.h>
#endif

using namespace clang;

const std::string F_NAME = "__CSM_lifetime_end";

struct VarInfo {
    VarInfo(std::string n, FullSourceLoc start, FullSourceLoc end, bool isL = false) :
        name(n), locStart(start), locEnd(end), isLoop(isL) {}

    std::string name = "";
    FullSourceLoc locStart;
    FullSourceLoc locEnd;
    bool isLoop = false;
};

// Visitor for adding curly braces
class BracesASTVisitor : public RecursiveASTVisitor<BracesASTVisitor> {
public:
  BracesASTVisitor(Rewriter &R, ASTContext &AC) : TheRewriter(R), AContext(AC) {}

  bool VisitStmt(Stmt* s) {

      // Process ifs without compound stmt
      if (isa<IfStmt>(s)) {
          IfStmt* ifs = cast<IfStmt>(s);
          Stmt* then = ifs->getThen();
          if (!isa<CompoundStmt>(*(then->children().begin()))) {
              SourceLocation SLB = then->getSourceRange().getBegin();
              SourceLocation SLE = then->getSourceRange().getEnd();
             // TheRewriter.InsertTextBefore(SLB, "{");
             // TheRewriter.InsertTextAfter(SLE, "}");
          }
      }

      return true;
  }

private:
  Rewriter &TheRewriter;
  ASTContext& AContext;
};

// Visitor for adding lifetime marks
class LifetimesASTVisitor : public RecursiveASTVisitor<LifetimesASTVisitor> {
public:
  LifetimesASTVisitor(Rewriter &R, ASTContext &AC) : TheRewriter(R), AContext(AC) {}

  bool VisitStmt(Stmt* s) {
      FullSourceLoc loc = AContext.getFullLoc(s->getSourceRange().getBegin());
      if (!vars.empty()) {
        FullSourceLoc varLoc = vars.back().locEnd;
        while (!vars.empty() && varLoc.isBeforeInTranslationUnitThan(loc)) {
            vars.pop_back();
            varLoc = vars.back().locEnd;
        }
      }

      // Process compound statements.
      if (isa<CompoundStmt>(s)) {
          Stmt* last = nullptr;
          std::vector<std::string> localVars;
          CompoundStmt *compoundStmt = cast<CompoundStmt>(s);

          for (auto* c : compoundStmt->children()) {
              if (isa<DeclStmt>(c)) {
                  DeclStmt* ds = cast<DeclStmt>(c);
                  for (auto* d : ds->decls()) {
                      VarDecl* varDecl = dyn_cast<VarDecl>(d);
                      if (varDecl && varDecl->isLocalVarDecl()) {
                          localVars.push_back(varDecl->getNameAsString());
                          vars.push_back(VarInfo(varDecl->getNameAsString(),
                             AContext.getFullLoc(varDecl->getSourceRange().getEnd()),
                             AContext.getFullLoc(compoundStmt->getSourceRange().getEnd()),
                             false));
                      }
                  }
              }
              last = c;
          }

          SourceLocation SL;
          if(last && !isa<ReturnStmt>(last) && !isa<BreakStmt>(last)
              && !isa<ContinueStmt>(last)) {
              SL = compoundStmt->getSourceRange().getEnd();
              for (const auto& v : localVars) {
                  TheRewriter.InsertTextBefore(SL, getFunctionCall(v));
              }
          }
      }


      // Process loops.
      if (isa<ForStmt>(s) || isa<DoStmt>(s) || isa<WhileStmt>(s)) {
          vars.push_back(VarInfo("",
                  AContext.getFullLoc(s->getSourceRange().getBegin()),
                  AContext.getFullLoc(s->getSourceRange().getEnd()),
                  true));
      }

      // Process returns.
      if (isa<ReturnStmt>(s)) {
          FullSourceLoc SL = AContext.getFullLoc(s->getSourceRange().getBegin());
          for(auto rit = vars.rbegin(); rit != vars.rend(); ++rit) {
              if (rit->name == "" && !rit->isLoop)
                  break;
              if (rit->name != "" && rit->locStart.isBeforeInTranslationUnitThan(SL)) {
                  TheRewriter.InsertTextBefore(SL, getFunctionCall(rit->name));
              }
          }
      }

      // Process breaks and continues.
      if (isa<BreakStmt>(s) || isa<ContinueStmt>(s)) {
          FullSourceLoc SL = AContext.getFullLoc(s->getSourceRange().getBegin());
          for(auto rit = vars.rbegin(); rit != vars.rend(); ++rit) {
              if (rit->name == "" && rit->isLoop)
                  break;
              if (rit->name != "" && rit->locStart.isBeforeInTranslationUnitThan(SL)) {
                  TheRewriter.InsertTextBefore(SL, getFunctionCall(rit->name));
              }
          }
      }

      return true;
  }

  bool VisitFunctionDecl(FunctionDecl *f) {
      // Only function definitions (with bodies), not declarations.
      if (f->hasBody()) {
          vars.push_back(VarInfo("",
                  AContext.getFullLoc(f->getSourceRange().getBegin()),
                  AContext.getFullLoc(f->getSourceRange().getEnd()),
                  false));

      }

      return true;
  }

private:
  std::vector<VarInfo> vars;
  Rewriter &TheRewriter;
  ASTContext& AContext;

  std::string getFunctionCall(std::string varName) {
       return F_NAME + "(sizeof(" + varName + "), &" + varName + ");";
  }
};

class LifetimesASTConsumer : public ASTConsumer {
public:
  LifetimesASTConsumer(Rewriter &R, ASTContext &AC) : Visitor(R, AC) {}

  // Override the method that gets called for each parsed top-level
  // declaration.
  virtual bool HandleTopLevelDecl(DeclGroupRef DR) {
    for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b)
      // Traverse the declaration using our AST visitor.
      Visitor.TraverseDecl(*b);
    return true;
  }

private:
  LifetimesASTVisitor Visitor;
};

class BracesASTConsumer : public ASTConsumer {
public:
  BracesASTConsumer(Rewriter &R, ASTContext &AC) : Visitor(R, AC) {}

  // Override the method that gets called for each parsed top-level
  // declaration.
  virtual bool HandleTopLevelDecl(DeclGroupRef DR) {
    for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b)
      // Traverse the declaration using our AST visitor.
      Visitor.TraverseDecl(*b);
    return true;
  }

private:
  BracesASTVisitor Visitor;
};

void emitLLVM(llvm::Module& M) {
    // Write instrumented module into the output file
    std::ofstream ofs("out.bc");
    llvm::raw_os_ostream ostream(ofs);

    // Write the module
    llvm::errs() << "Saving the module to out.bc " << "\n";
    llvm::WriteBitcodeToFile(&M, ostream);
}

void instrumentAndEmitLLVM(llvm::Module& M) {
    for (auto Fit = M.begin(), E = M.end(); Fit != E; ++Fit) {
        for (auto Iit = inst_begin(&*Fit), End = inst_end(&*Fit); Iit != End; ++Iit) {
            if (llvm::CallInst* CI = llvm::dyn_cast<llvm::CallInst>(&*Iit)) {
                llvm::Function* f = CI->getCalledFunction();
                std::string name = f->getName().str();
                if(name == F_NAME) {
                    llvm::Function* lef = llvm::Intrinsic::getDeclaration(&M,
                                                llvm::Intrinsic::lifetime_end);
                    CI->setCalledFunction(lef);
                }
            }
        }
    }

    emitLLVM(M);
}

void setCompilerInstance(CompilerInstance& TheCompInst, std::string path) {
    // CompilerInstance will hold the instance of the Clang compiler for us,
    // managing the various objects needed to run the compiler.
    TheCompInst.createDiagnostics();

    LangOptions &lo = TheCompInst.getLangOpts();
    lo.CPlusPlus = 1;

    // Initialize target info with the default triple for our platform.
    auto TO = std::make_shared<TargetOptions>();
    TO->Triple = llvm::sys::getDefaultTargetTriple();
    TargetInfo *TI =
        TargetInfo::CreateTargetInfo(TheCompInst.getDiagnostics(), TO);
    TheCompInst.setTarget(TI);

    TheCompInst.createFileManager();
    FileManager &FileMgr = TheCompInst.getFileManager();
    TheCompInst.createSourceManager(FileMgr);
    SourceManager &SourceMgr = TheCompInst.getSourceManager();
    TheCompInst.createPreprocessor(TU_Module);
    TheCompInst.createASTContext();

    // Set the main file handled by the source manager to the input file.
    const FileEntry *FileIn = FileMgr.getFile(path);
    SourceMgr.setMainFileID(
        SourceMgr.createFileID(FileIn, SourceLocation(), SrcMgr::C_User));
    TheCompInst.getDiagnosticClient().BeginSourceFile(
        TheCompInst.getLangOpts(), &TheCompInst.getPreprocessor());
}

template<typename T>
std::string processFile(std::string path) {
    CompilerInstance TheCompInst;
    setCompilerInstance(TheCompInst, path);
    SourceManager &SourceMgr = TheCompInst.getSourceManager();

    // A Rewriter helps us manage the code rewriting task.
    Rewriter TheRewriter;
    TheRewriter.setSourceMgr(SourceMgr, TheCompInst.getLangOpts());

    // Create an AST consumer instance which is going to get called by
    // ParseAST.
    T TheConsumer(TheRewriter, TheCompInst.getASTContext());

    // Parse the file to AST, registering our consumer as the AST consumer.
    ParseAST(TheCompInst.getPreprocessor(), &TheConsumer,
             TheCompInst.getASTContext());

    // At this point the rewriter's buffer should be full with the rewritten
    // file contents.
    const RewriteBuffer* RewriteBuf =
        TheRewriter.getRewriteBufferFor(SourceMgr.getMainFileID());

    if (RewriteBuf) {
        return std::string(RewriteBuf->begin(), RewriteBuf->end());
    }
    else {
        std::ifstream ifs(path);
        return std::string((std::istreambuf_iterator<char>(ifs)),
                            (std::istreambuf_iterator<char>()));
    }
}

void runTransformations(std::string path, std::vector<const char*>& args) {
    llvm::errs() << "--------------------\n";
    // Transformation 1: add curly braces where needed.
    auto code = processFile<BracesASTConsumer>(path);
    std::ofstream outfile ("tmp1.c");
    std::string allCode = "void " + F_NAME + "(long int, void*);\n" + code;
    outfile << allCode << std::endl;
    outfile.close();
    llvm::errs() << code << "\n";

    llvm::errs() << "--------------------\n";
    // Transformation 2: add lifetime marks.
    code = processFile<LifetimesASTConsumer>("tmp1.c");
    std::ofstream outfile2 ("tmp2.c");
    outfile2 << code << std::endl;
    outfile2.close();
    llvm::errs() << code << "\n";
    llvm::errs() << "--------------------\n";

    CompilerInstance TheCompInst;
    setCompilerInstance(TheCompInst, "tmp2.c");
    args.push_back("tmp2.c");
    std::unique_ptr<CompilerInvocation> CI(createInvocationFromCommandLine(args));

    TheCompInst.setInvocation(CI.release());

    // Get llvm module.
    EmitLLVMOnlyAction *Act = new EmitLLVMOnlyAction();

    TheCompInst.getTargetOpts().Triple = llvm::sys::getDefaultTargetTriple();
    if (TheCompInst.ExecuteAction(*Act)) {
        llvm::Module* M = Act->takeModule().release();
        instrumentAndEmitLLVM(*M);
    }

    // Delete temporary C files.
    std::remove("tmp1.c");
    std::remove("tmp2.c");
    delete(Act);
}

int main(int argc, char *argv[]) {
    if (argc != 2) {
      llvm::errs() << "Usage: scopes-marker <filename>\n";
      return 1;
    }

    std::vector<const char *> aargs;
    aargs.push_back("clang");
    aargs.push_back("-g");

    runTransformations(argv[1], aargs);

    return 0;
}
