//------------------------------------------------------------------------------
// Clang rewriter sample. Demonstrates:
//
// * How to use RecursiveASTVisitor to find interesting AST nodes.
// * How to use the Rewriter API to rewrite the source code.
//
// Eli Bendersky (eliben@gmail.com)
// This code is in the public domain
//------------------------------------------------------------------------------
#include <cstdio>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

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

using namespace clang;
struct VarInfo {
    VarInfo(std::string n, FullSourceLoc start, FullSourceLoc end, bool isL = false) :
        name(n), locStart(start), locEnd(end), isLoop(isL) {}

    std::string name = "";
    FullSourceLoc locStart;
    FullSourceLoc locEnd;
    bool isLoop = false;
};

// By implementing RecursiveASTVisitor, we can specify which AST nodes
// we're interested in by overriding relevant methods.
class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
public:
  MyASTVisitor(Rewriter &R, ASTContext &AC) : TheRewriter(R), AContext(AC) {}

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
                  std::string s = "__CSM__lifetimeEnd(" + v + ");\n";
                  TheRewriter.InsertTextBefore(SL, s);
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
                  std::string s = "__CSM__lifetimeEnd(" + rit->name + ");\n";
                  TheRewriter.InsertTextBefore(SL, s);
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
                  std::string s = "__CSM__lifetimeEnd(" + rit->name + ");\n";
                  TheRewriter.InsertTextBefore(SL, s);
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
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public ASTConsumer {
public:
  MyASTConsumer(Rewriter &R, ASTContext &AC) : Visitor(R, AC) {}

  // Override the method that gets called for each parsed top-level
  // declaration.
  virtual bool HandleTopLevelDecl(DeclGroupRef DR) {
    for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b)
      // Traverse the declaration using our AST visitor.
      Visitor.TraverseDecl(*b);
    return true;
  }

private:
  MyASTVisitor Visitor;
};

void instrumentAndEmitLLVM(llvm::Module& M) {
   /* for(llvm::Function& F : M) {
        for(auto& I : F) {
            I.dump();
        }
    }*/
}

int main(int argc, char *argv[]) {
    if (argc != 2) {
      llvm::errs() << "Usage: rewritersample <filename>\n";
      return 1;
    }

    // CompilerInstance will hold the instance of the Clang compiler for us,
    // managing the various objects needed to run the compiler.
    CompilerInstance TheCompInst;
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

    // A Rewriter helps us manage the code rewriting task.
    Rewriter TheRewriter;
    TheRewriter.setSourceMgr(SourceMgr, TheCompInst.getLangOpts());

    // Set the main file handled by the source manager to the input file.
    const FileEntry *FileIn = FileMgr.getFile(argv[1]);
    SourceMgr.setMainFileID(
        SourceMgr.createFileID(FileIn, SourceLocation(), SrcMgr::C_User));
    TheCompInst.getDiagnosticClient().BeginSourceFile(
        TheCompInst.getLangOpts(), &TheCompInst.getPreprocessor());

    // Create an AST consumer instance which is going to get called by
    // ParseAST.
    MyASTConsumer TheConsumer(TheRewriter, TheCompInst.getASTContext());

    // Parse the file to AST, registering our consumer as the AST consumer.
    ParseAST(TheCompInst.getPreprocessor(), &TheConsumer,
             TheCompInst.getASTContext());

    std::vector<const char *> aargs;
    aargs.push_back("clang");
    aargs.push_back(argv[1]);

    std::unique_ptr<CompilerInvocation> CI(createInvocationFromCommandLine(aargs));

    TheCompInst.setInvocation(CI.release());

    // Get llvm module.
    EmitLLVMOnlyAction *Act = new EmitLLVMOnlyAction();

    TheCompInst.getTargetOpts().Triple = llvm::sys::getDefaultTargetTriple();
    if (TheCompInst.ExecuteAction(*Act)) {
        llvm::Module* M = Act->takeModule().release();
        instrumentAndEmitLLVM(*M);
    }

    // At this point the rewriter's buffer should be full with the rewritten
    // file contents.
    const RewriteBuffer *RewriteBuf =
        TheRewriter.getRewriteBufferFor(SourceMgr.getMainFileID());
    llvm::outs() << std::string(RewriteBuf->begin(), RewriteBuf->end());

    //TODO delete module

    return 0;
}
