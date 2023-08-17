#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <queue>
#include <string.h>
#include <string>
#include <system_error>
#include <utility>
#include <vector>
#include <ctype.h>

using namespace llvm;
using namespace llvm::sys;

FILE *pFile;

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns one of these for known things.
enum TOKEN_TYPE {

  IDENT = -1,        // [a-zA-Z_][a-zA-Z_0-9]*
  ASSIGN = int('='), // '='

  // delimiters
  LBRA = int('{'),  // left brace
  RBRA = int('}'),  // right brace
  LPAR = int('('),  // left parenthesis
  RPAR = int(')'),  // right parenthesis
  SC = int(';'),    // semicolon
  COMMA = int(','), // comma

  // types
  INT_TOK = -2,   // "int"
  VOID_TOK = -3,  // "void"
  FLOAT_TOK = -4, // "float"
  BOOL_TOK = -5,  // "bool"

  // keywords
  EXTERN = -6,  // "extern"
  IF = -7,      // "if"
  ELSE = -8,    // "else"
  WHILE = -9,   // "while"
  RETURN = -10, // "return"
  // TRUE   = -12,     // "true"
  // FALSE   = -13,     // "false"

  // literals
  INT_LIT = -14,   // [0-9]+
  FLOAT_LIT = -15, // [0-9]+.[0-9]+
  BOOL_LIT = -16,  // "true" or "false" key words

  // logical operators
  AND = -17, // "&&"
  OR = -18,  // "||"

  // operators
  PLUS = int('+'),    // addition or unary plus
  MINUS = int('-'),   // substraction or unary negative
  ASTERIX = int('*'), // multiplication
  DIV = int('/'),     // division
  MOD = int('%'),     // modular
  NOT = int('!'),     // unary negation

  // comparison operators
  EQ = -19,      // equal
  NE = -20,      // not equal
  LE = -21,      // less than or equal to
  LT = int('<'), // less than
  GE = -23,      // greater than or equal to
  GT = int('>'), // greater than

  // special tokens
  EOF_TOK = 0, // signal end of file

  // invalid
  INVALID = -100 // signal invalid token
};

// TOKEN struct is used to keep track of information about a token
struct TOKEN {
  int type = -100;
  std::string lexeme;
  int lineNo;
  int columnNo;
};

static std::string IdentifierStr; // Filled in if IDENT
static int IntVal;                // Filled in if INT_LIT
static bool BoolVal;              // Filled in if BOOL_LIT
static float FloatVal;            // Filled in if FLOAT_LIT
static std::string StringVal;     // Filled in if String Literal
static int lineNo, columnNo;

static TOKEN returnTok(std::string lexVal, int tok_type) {
  TOKEN return_tok;
  return_tok.lexeme = lexVal;
  return_tok.type = tok_type;
  return_tok.lineNo = lineNo;
  return_tok.columnNo = columnNo - lexVal.length() - 1;
  return return_tok;
}

// Read file line by line -- or look for \n and if found add 1 to line number
// and reset column number to 0
/// gettok - Return the next token from standard input.
static TOKEN gettok() {

  static int LastChar = ' ';
  static int NextChar = ' ';

  // Skip any whitespace.
  while (isspace(LastChar)) {
    if (LastChar == '\n' || LastChar == '\r') {
      lineNo++;
      columnNo = 1;
    }
    LastChar = getc(pFile);
    columnNo++;
  }

  if (isalpha(LastChar) ||
      (LastChar == '_')) { // identifier: [a-zA-Z_][a-zA-Z_0-9]*
    IdentifierStr = LastChar;
    columnNo++;

    while (isalnum((LastChar = getc(pFile))) || (LastChar == '_')) {
      IdentifierStr += LastChar;
      columnNo++;
    }

    if (IdentifierStr == "int")
      return returnTok("int", INT_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "float")
      return returnTok("float", FLOAT_TOK);
    if (IdentifierStr == "void")
      return returnTok("void", VOID_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "extern")
      return returnTok("extern", EXTERN);
    if (IdentifierStr == "if")
      return returnTok("if", IF);
    if (IdentifierStr == "else")
      return returnTok("else", ELSE);
    if (IdentifierStr == "while")
      return returnTok("while", WHILE);
    if (IdentifierStr == "return")
      return returnTok("return", RETURN);
    if (IdentifierStr == "true") {
      BoolVal = true;
      return returnTok("true", BOOL_LIT);
    }
    if (IdentifierStr == "false") {
      BoolVal = false;
      return returnTok("false", BOOL_LIT);
    }

    return returnTok(IdentifierStr.c_str(), IDENT);
  }

  if (LastChar == '=') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // EQ: ==
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("==", EQ);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("=", ASSIGN);
    }
  }

  if (LastChar == '{') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("{", LBRA);
  }
  if (LastChar == '}') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("}", RBRA);
  }
  if (LastChar == '(') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("(", LPAR);
  }
  if (LastChar == ')') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(")", RPAR);
  }
  if (LastChar == ';') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(";", SC);
  }
  if (LastChar == ',') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(",", COMMA);
  }

  if (isdigit(LastChar) || LastChar == '.') { // Number: [0-9]+.
    std::string NumStr;

    if (LastChar == '.') { // Floatingpoint Number: .[0-9]+
      do {
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      FloatVal = strtof(NumStr.c_str(), nullptr);
      return returnTok(NumStr, FLOAT_LIT);
    } else {
      do { // Start of Number: [0-9]+
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      if (LastChar == '.') { // Floatingpoint Number: [0-9]+.[0-9]+)
        do {
          NumStr += LastChar;
          LastChar = getc(pFile);
          columnNo++;
        } while (isdigit(LastChar));

        FloatVal = strtof(NumStr.c_str(), nullptr);
        return returnTok(NumStr, FLOAT_LIT);
      } else { // Integer : [0-9]+
        IntVal = strtod(NumStr.c_str(), nullptr);
        return returnTok(NumStr, INT_LIT);
      }
    }
  }

  if (LastChar == '&') {
    NextChar = getc(pFile);
    if (NextChar == '&') { // AND: &&
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("&&", AND);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("&", int('&'));
    }
  }

  if (LastChar == '|') {
    NextChar = getc(pFile);
    if (NextChar == '|') { // OR: ||
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("||", OR);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("|", int('|'));
    }
  }

  if (LastChar == '!') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // NE: !=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("!=", NE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("!", NOT);
      ;
    }
  }

  if (LastChar == '<') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // LE: <=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("<=", LE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("<", LT);
    }
  }

  if (LastChar == '>') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // GE: >=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok(">=", GE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok(">", GT);
    }
  }

  if (LastChar == '/') { // could be division or could be the start of a comment
    LastChar = getc(pFile);
    columnNo++;
    if (LastChar == '/') { // definitely a comment
      do {
        LastChar = getc(pFile);
        columnNo++;
      } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

      if (LastChar != EOF)
        return gettok();
    } else
      return returnTok("/", DIV);
  }

  // Check for end of file.  Don't eat the EOF.
  if (LastChar == EOF) {
    columnNo++;
    return returnTok("0", EOF_TOK);
  }

  // Otherwise, just return the character as its ascii value.
  int ThisChar = LastChar;
  std::string s(1, ThisChar);
  LastChar = getc(pFile);
  columnNo++;
  return returnTok(s, int(ThisChar));
}

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static TOKEN CurTok;
static std::deque<TOKEN> tok_buffer;

static TOKEN getNextToken() {

  if (tok_buffer.size() == 0)
    tok_buffer.push_back(gettok());

  TOKEN temp = tok_buffer.front();
  tok_buffer.pop_front();

  return CurTok = temp;
}

static void putBackToken(TOKEN tok) { tok_buffer.push_front(tok);}
static TOKEN peekToken() {
    if (tok_buffer.size() == 0)
      tok_buffer.push_back(gettok());
  
  return tok_buffer.front();
} //returns the top value without removing it.

//===----------------------------------------------------------------------===//
// AST nodes
//===----------------------------------------------------------------------===//

static std::string getIndent(int depth) {
  std::string ret = "";
  for (int i = 0; i < depth; i++) {
    ret =  "   " + ret;
  }
  return ret;
}

/// ASTnode - Base class for all AST nodes.
class ASTnode {
public:
  virtual ~ASTnode() {}
  virtual Value *codegen() = 0;
  virtual std::string getName() {return "";}
  virtual bool isVariable() {return false;}
  virtual std::string to_string(int depth) const {return "";};
};

// INTERGER NODES.

/// IntASTnode - Class for integer literals like 1, 2, 10,
class IntASTnode : public ASTnode {
  int Val; int lineNumber;

public: 
  IntASTnode(int val, int number) : Val(val), lineNumber(number) {}
  virtual Value *codegen() override;
  virtual std::string getName() {return "";}
  virtual bool isVariable() override {return false;}
  virtual std::string to_string(int depth) const override {
      return getIndent(depth) + "Integer Value: " + std::to_string(Val) + "\n";
  };
};

/// FloatASTnode - Class for integer literals like 1, 2, 10,
class FloatASTnode : public ASTnode {
  float Val; int lineNumber;

public: 
  FloatASTnode(float val, int number) : Val(val), lineNumber(number) {}
  virtual Value *codegen() override;
  virtual std::string getName() {return "";}
  virtual bool isVariable() override {return false;}
  virtual std::string to_string(int depth) const override {
      return getIndent(depth) + "Floating point Value: " + std::to_string(Val) + "\n";
  };
};

/// BoolASTnode - Class for integer literals like 1, 2, 10,
class BoolASTnode : public ASTnode {
  bool Val; int lineNumber;

public: 
  BoolASTnode(bool val, int number) : Val(val), lineNumber(number) {}
  virtual Value *codegen() override;
  virtual std::string getName() {return "";}
  virtual bool isVariable() override {return false;}
  virtual std::string to_string(int depth) const override {
      return getIndent(depth) + "Boolean Value: " + std::to_string(Val) + "\n";
  };
};

/* add other AST nodes as nessasary */

/// VariableASTnode - Class for variable identifiers.
class VariableASTnode : public ASTnode {
  std::string Name; std::string Type; int lineNumber;
public:
  VariableASTnode(std::string name, std::string type, int number) : Name(name), Type(type), lineNumber(number) {}
  virtual Value *codegen() override;
  virtual bool isVariable() override {return true;}
  virtual std::string getType() {return Type;}
  virtual int getLineNumber() {return lineNumber;}
  virtual std::string getName() override {return Name;}
  virtual std::string to_string(int depth) const override {
    return getIndent(depth) + "Variable declaration " + Name + " of Type " + Type + "\n";
  };
};

/// VariableReferenceASTnode - Class for variable identifiers.
class VariableReferenceASTnode : public ASTnode {
  std::string Name; int lineNumber;
public:
  VariableReferenceASTnode(std::string name, int number) : Name(name), lineNumber(number) {}
  virtual Value *codegen() override;
  virtual std::string getName() override {return Name;}
  virtual bool isVariable() override {return false;}
  virtual std::string to_string(int depth) const override {
    return getIndent(depth) + "Variable reference with name: " + Name + "\n";
  };
};

class ProtoAST : public ASTnode {
  std::string Identifier; std::string Name; std::vector<std::string> Params; std::vector<std::string> Types;
  //std::vector<std::pair<VarTypeASTnode, std::string>> Params;
public:
  ProtoAST(std::string identifier, std::string name, std::vector<std::string> params, std::vector<std::string> types) : Identifier(identifier), Name(name), Params(std::move(params)), Types(std::move(types)) {}
  virtual Function *codegen() override;
  virtual std::string getName() override {return Name;}
  virtual bool isVariable() override {return false;}
  virtual std::string to_string(int depth) const override {
    std::string ret = "Function Proto.  return type: " + Identifier + " Name: " + Name + "\n";
    for(int i = 0; i < Params.size(); i++) {
      ret = ret + "   Param Declaration. Type: " + Types[i] + " with Name: " + Params[i] + "\n"; 
    } 
    return ret;
  };
};

// class to store function and their body.  contains a Proto function and a body.
class BodyASTnode : public ASTnode {
  std::vector<std::unique_ptr<ASTnode>> Content;
public:
  BodyASTnode(std::vector<std::unique_ptr<ASTnode>> content) : Content(std::move(content))  {}
  virtual Value *codegen() override;
  virtual std::string getName() {return "";}
  virtual bool isVariable() override {return false;}
  virtual std::string to_string(int depth) const override {
    std::string ret = getIndent(depth) + "Body Block Start:\n";

    for (auto & i : Content) {
      ret = ret + i->to_string(depth+1);
    }

    return ret + getIndent(depth) + "Body Block end.\n";
  };
};

// class to store function and their body.  contains a Proto function and a body.
class FunctionASTnode : public ASTnode {
  std::unique_ptr<ProtoAST> Proto; std::unique_ptr<ASTnode> Body;
public:
  FunctionASTnode(std::unique_ptr<ProtoAST> Proto, std::unique_ptr<ASTnode> Body) : Proto(std::move(Proto)), Body(std::move(Body))  {}
  virtual Function *codegen() override;
  virtual std::string getName() {return "";}
  virtual bool isVariable() override {return false;}
  virtual std::string to_string(int depth) const override {
    std::string ret = Proto->to_string(0) + "----------------------------------------------------------------- \n";
    
    ret = ret + Body->to_string(depth+1);

    return ret;
  };
};

// class to store function and their body.  contains a Proto function and a body.
class CalleeASTnode : public ASTnode {
  std::string Name; std::vector<std::unique_ptr<ASTnode>> Args; int lineNumber;
public:
  CalleeASTnode(std::string name, std::vector<std::unique_ptr<ASTnode>> args, int number) : Name(name), Args(std::move(args)), lineNumber(number)  {}
  virtual Value *codegen() override;
  virtual std::string getName() {return "";}
  virtual bool isVariable() override {return false;}
  virtual std::string to_string(int depth) const override {
    std::string ret =  getIndent(depth) + "Function call with Name: " + Name + "\n";

    for (auto & i : Args) {
      ret = ret + i->to_string(depth+1);
    }
    return ret + getIndent(depth) + "Function end.\n";
  };
};

// class to store function and their body.  contains a Proto function and a body.
class UnaryASTnode : public ASTnode {
  std::string Prefix; int intType; std::unique_ptr<ASTnode> Next; int lineNumber;
public:
  UnaryASTnode(std::string prefix, int type, std::unique_ptr<ASTnode> next, int number) : Prefix(prefix), intType(type), Next(std::move(next)), lineNumber(number)  {}
  virtual Value *codegen() override;
  virtual std::string getName() {return "";}
  virtual bool isVariable() override {return false;}
  virtual std::string to_string(int depth) const override {
    return getIndent(depth) + "Unary Definition node with Prefix: '" + Prefix + "'\n" + Next->to_string(depth+1);
  };
};

// class to store function and their body.  contains a Proto function and a body.
class BinaryASTnode : public ASTnode {
  std::string Op; int intType; std::unique_ptr<ASTnode> LHS; std::unique_ptr<ASTnode> RHS; int lineNumber;
public:
  BinaryASTnode(std::string op, int t, std::unique_ptr<ASTnode> lhs, std::unique_ptr<ASTnode> rhs, int number) : Op(op), intType(t), LHS(std::move(lhs)), RHS(std::move(rhs)), lineNumber(number)  {}
  virtual Value *codegen() override;
  virtual std::string getName() {return "";}
  virtual bool isVariable() override {return false;}
  virtual std::string to_string(int depth) const override {
    return getIndent(depth) + "Binary Operator.  Operator: " + Op + "\n" + LHS->to_string(depth+1) + RHS->to_string(depth+1) + getIndent(depth) + "Binary Operator end.\n";
  };
};

/// VariableReferenceASTnode - Class for variable identifiers.
class ReturnASTnode : public ASTnode {
  std::unique_ptr<ASTnode> Bin; bool Flag; int lineNumber;
public:
  ReturnASTnode(std::unique_ptr<ASTnode> bin, bool flag, int number) : Bin(std::move(bin)), Flag(flag), lineNumber(number) {}
  virtual Value *codegen() override;
  virtual std::string getName() {return "";}
  virtual bool isVariable() override {return false;}
  virtual std::string to_string(int depth) const override {
    if (!Flag) {return getIndent(depth) + "Return Statement. \n" + getIndent(depth+1) + " Return statement type: void \n";}
    return getIndent(depth) + "Return Statement.\n" + Bin->to_string(depth+1) + getIndent(depth) + "Return Statement end.\n";
  };
};

/// VariableReferenceASTnode - Class for variable identifiers.
class IfASTnode : public ASTnode {
  std::unique_ptr<ASTnode> Exp; std::unique_ptr<ASTnode> Body; std::unique_ptr<ASTnode> EBody; bool Flag;
public:
  IfASTnode(std::unique_ptr<ASTnode> exp, std::unique_ptr<ASTnode> body, std::unique_ptr<ASTnode> ebody, bool flag) : Exp(std::move(exp)), Body(std::move(body)), EBody(std::move(ebody)), Flag(flag) {}
  virtual Value *codegen() override;
  virtual std::string getName() {return "";}
  virtual bool isVariable() override {return false;}
  virtual std::string to_string(int depth) const override {
    std::string ret = getIndent(depth) + "If statement start.\n" + getIndent(depth+1) + "Expression start\n" + Exp->to_string(depth+2) + getIndent(depth+1) + "Expression end.\n" + getIndent(depth+1) + "Main Body start.\n" + Body->to_string(depth+2) + getIndent(depth+1) + "Main Body end.\n";

    if (Flag) {ret = ret + getIndent(depth+1) + "Else statement start.\n" + EBody->to_string(depth+2) + getIndent(depth+1) + "Else statement end.\n";}
    return ret + getIndent(depth) + "If statement end.\n";
  };
};

/// VariableReferenceASTnode - Class for variable identifiers.
class WhileASTnode : public ASTnode {
  std::unique_ptr<ASTnode> Exp; std::unique_ptr<ASTnode> Body;
public:
  WhileASTnode(std::unique_ptr<ASTnode> exp, std::unique_ptr<ASTnode> body) : Exp(std::move(exp)), Body(std::move(body)) {}
  virtual Value *codegen() override;
  virtual std::string getName() {return "";}
  virtual bool isVariable() override {return false;}
  virtual std::string to_string(int depth) const override {
    return getIndent(depth) + "While loop start.\n" + getIndent(depth+1) + "Expression start.\n" + Exp->to_string(depth+2) + getIndent(depth+1) + "Expression end.\n" + Body->to_string(depth+1) + getIndent(depth) + "While loop end.\n";
  };
};

/// ProgASTnode - Class for Program AST.
class ProgASTnode : public ASTnode {
  std::vector<std::unique_ptr<ProtoAST>> ExternList; std::vector<std::unique_ptr<ASTnode>> DecList;

public: 
  ProgASTnode(std::vector<std::unique_ptr<ProtoAST>> externlist, std::vector<std::unique_ptr<ASTnode>> DecList) : ExternList(std::move(externlist)), DecList(std::move(DecList)) {}
  virtual Value *codegen() override;
  virtual std::string getName() {return "";}
  virtual bool isVariable() override {return false;}
  virtual std::string to_string(int depth) const override {
    std::string ret = "";
    
    for (auto & i : ExternList) {
      if (i->isVariable()) {}
      ret = ret + "extern " + i->to_string(0);
    }

    for (auto & i : DecList) {
      if (i->isVariable()) {
        ret =  ret + "Global " + i->to_string(0);
      } else {
        ret = ret + i->to_string(0);
      }
    }
    
    return ret;
  };
  bool IsEmpty() {
    return (ExternList.size() == 0 && DecList.size() == 0);
  }
};




//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

bool check = true; //check if an error has occured.

/// LogError* - These are little helper functions for error handling.
std::unique_ptr<ASTnode> LogError(const char *Str) {
  if (check) {fprintf(stderr, "Error: %s At line number: %d\n", Str, CurTok.lineNo); check = false;}
  return nullptr;
}

/// LogError* - These are little helper functions for error handling.
std::unique_ptr<ProtoAST> LogErrorP(const char *Str) {
  if (check) {fprintf(stderr, "Error: %s At line number: %d\n", Str, CurTok.lineNo); check = false;}
  return nullptr;
}

/// BinopPrecedence - This holds the precedence for each binary operator that is
/// defined.
static std::map<char, int> BinopPrecedence;

/// GetTokPrecedence - Get the precedence of the pending binary operator token.
static int GetTokPrecedence() {
  // Make sure it's a declared binop.
  int TokPrec = BinopPrecedence[CurTok.type];
  if (TokPrec <= 0)
    return -1;
  return TokPrec;
}

/* Add function calls for each production */

static std::string ParseType() {
  switch(CurTok.type) {
    case INT_TOK:
      return "Int";
    case FLOAT_TOK:
      return "Float";
    case BOOL_TOK:
      return "bool";
    case VOID_TOK:
      return "void";
    default:
      return "error";
  }
}

static std::unique_ptr<ProtoAST> ParsePrototype(std::string Type, std::string Name) {

  if (CurTok.type != LPAR)
    return LogErrorP("Expected '(' in prototype");
  getNextToken(); // eat '('

  std::vector<std::string> ArgNames;
  std::vector<std::string> ArgTypes;
  std::string T = ParseType();
  
  while (T.compare("error") != 0) {

    if (CurTok.type == VOID_TOK) {
      getNextToken(); // eat void.
    } else {
        ArgTypes.push_back(T);
        getNextToken(); // eat the type

        if (CurTok.type != IDENT)
          return LogErrorP("Expected variable name in function");

      //ArgNames.push_back(IdentifierStr);
      ArgNames.push_back(IdentifierStr);
      getNextToken(); // eat tok_identifier
    }

    if (CurTok.type == COMMA) {
      getNextToken(); // eats ','
      T = ParseType(); // gets variable type.
      if (T.compare("error") == 0) {return LogErrorP("Expected variable type declaration.");} //checks if next token is valid.
    } else {
      if (CurTok.type == RPAR) {T = "error";} else {return LogErrorP("Error in function variable declaration");} // enforces break of while loop.
    } 
  }    

  if (CurTok.type != RPAR)
    return LogErrorP("Expected ')' in prototype");

  // success.
  getNextToken(); // eat ')'.

  return std::make_unique<ProtoAST>(Type, Name, std::move(ArgNames), std::move(ArgTypes));
}

/// external ::= 'extern' prototype
static std::vector<std::unique_ptr<ProtoAST>> ParseExtern() {  
  std::vector<std::unique_ptr<ProtoAST>> ExternList;
  getNextToken(); // eat extern.

  std::string FnName; 
  std::string FnType = ParseType(); // get the function type.

  if (FnType.compare("error") == 0) {fprintf(stderr, "Expected Function type in declaration."); return std::vector<std::unique_ptr<ProtoAST>>();} //throw error if incrorect.
  getNextToken(); // eat type.

  if (CurTok.type != IDENT) {fprintf(stderr, "Expected Function name in declaration."); return std::vector<std::unique_ptr<ProtoAST>>();}

  FnName = IdentifierStr;
  getNextToken(); // eat tok_identifier

  auto V = ParsePrototype(FnType, FnName);

  if(!V) {return std::vector<std::unique_ptr<ProtoAST>>();} //exit program if error found.

  if (CurTok.type != SC) {fprintf(stderr, "Missing semi-colon."); return std::vector<std::unique_ptr<ProtoAST>>();}
  getNextToken();

  //ExternList.push_back(std::move(V)); //add the prototype to the extern list
  ExternList.push_back(std::move(V));

  while (CurTok.type == EXTERN) {
    getNextToken(); // eat extern
      std::string FnName; 
      FnType = ParseType(); // get the function type.

    if (FnType.compare("error") == 0) {fprintf(stderr, "Expected Function type in declaration."); return std::vector<std::unique_ptr<ProtoAST>>();} //throw error if incrorect.
    getNextToken(); // eat type.

    if (CurTok.type != IDENT) {fprintf(stderr, "Expected Function name in declaration."); return std::vector<std::unique_ptr<ProtoAST>>();}

    FnName = IdentifierStr;
    getNextToken(); // eat tok_identifier
    V = ParsePrototype(FnType, FnName);
    if (!V) {return std::vector<std::unique_ptr<ProtoAST>>();}
    if (CurTok.type != SC) {fprintf(stderr, "Missing semi-colon."); return std::vector<std::unique_ptr<ProtoAST>>();}
    getNextToken(); // eat ';'
    ExternList.push_back(std::move(V));
    V.reset();
  }

  return ExternList;
}
static std::unique_ptr<ASTnode> ParseUnary();
static std::unique_ptr<ASTnode> ParseExpr(int ExprPrec, std::unique_ptr<ASTnode> LHS) {
  // If this is a binop, find its precedence.
  while (true) {
    int TokPrec = GetTokPrecedence();
    int intType = CurTok.type;

    // If this is a binop that binds at least as tightly as the current binop,
    // consume it, otherwise we are done.
    if (TokPrec < ExprPrec)
      return LHS;

    // Okay, we know this is a binop.
    std::string BinOp = CurTok.lexeme.c_str();
    getNextToken(); // eat binop

    // Parse the primary expression after the binary operator.
    auto RHS = ParseUnary();
    if (!RHS)
      return nullptr;

    // If BinOp binds less tightly with RHS than the operator after RHS, let
    // the pending operator take RHS as its LHS.
    int NextPrec = GetTokPrecedence();
    if (TokPrec < NextPrec) {
      RHS = ParseExpr(TokPrec + 1, std::move(RHS));
      if (!RHS)
        return nullptr;
    }

    // Merge LHS/RHS.
    LHS =
        std::make_unique<BinaryASTnode>(BinOp , intType, std::move(LHS), std::move(RHS), CurTok.lineNo);
  }
}
static std::unique_ptr<ASTnode> ParseExpression();
static std::vector<std::unique_ptr<ASTnode>> ParseArgs() {
  std::vector<std::unique_ptr<ASTnode>> args;
  auto V = ParseExpression();
  if (!V) {LogError("Invalid Functiona call arguments"); return std::vector<std::unique_ptr<ASTnode>>();}
  args.push_back(std::move(V));
  
  while (CurTok.type != RPAR) {
    if (CurTok.type != COMMA) {LogError("Error parsing binary expression.2"); return std::vector<std::unique_ptr<ASTnode>>();}
    getNextToken(); // eat ','
    V = ParseExpression();
    if (!V) {LogError("Invalid Functiona call arguments"); return std::vector<std::unique_ptr<ASTnode>>();}
    args.push_back(std::move(V));
  }

  return args;
}

static std::unique_ptr<ASTnode> ParseCallee(std::string FName) {
  getNextToken(); // eat '('
  std::vector<std::unique_ptr<ASTnode>> V;
  if (CurTok.type != RPAR) {V = ParseArgs();} else {V = std::vector<std::unique_ptr<ASTnode>>();}

  if (CurTok.type != RPAR) {return LogError("Missing ')' in Function call.");}
  getNextToken(); // eact ')'
  return std::make_unique<CalleeASTnode>(FName, std::move(V), CurTok.lineNo);
}

static std::unique_ptr<ASTnode> ParseIdentifiers() {
  switch(CurTok.type) 
  {
    case IDENT:
    {
      std::string Name = IdentifierStr;
      getNextToken(); // eact identifier.
      if (CurTok.type == LPAR) { //TO DO
        auto V = ParseCallee(Name);
        if (!V) {LogError("Invalid function reference.");}
        return V;
      }
      return std::make_unique<VariableReferenceASTnode>(Name, CurTok.lineNo);
    }
    default:
    {
      switch(CurTok.type) 
      {
        case INT_LIT:
        {
          getNextToken();
          return std::make_unique<IntASTnode>(IntVal, CurTok.lineNo);
        }
        case BOOL_LIT:
        {
          getNextToken();
          return std::make_unique<BoolASTnode>(BoolVal, CurTok.lineNo);
        }
        case FLOAT_LIT:
        {
          getNextToken();
          return std::make_unique<FloatASTnode>(FloatVal, CurTok.lineNo);
        }
        default:
        {
          return nullptr;
        }
      }
    }
  }
}
static std::unique_ptr<ASTnode> ParseExpression();
static std::unique_ptr<ASTnode> ParseRest() {
  switch(CurTok.type)
  {
    case LPAR:
    {
      getNextToken(); //eat '('
      auto V = ParseExpression();
      if (!V) {return nullptr;}
      if (CurTok.type != RPAR) {return nullptr;}
      getNextToken(); // eat ')'
      return V;
    }
    default:
    {
      return ParseIdentifiers();
    } 
  }
}

static std::unique_ptr<ASTnode> ParseUnary() {

  switch (CurTok.type)
  {
    case MINUS: 
    {
      getNextToken(); // eat '-'
      auto V = ParseUnary();
      if (!V) {return LogError("Error in parsing binary expression.4");}
      return std::make_unique<UnaryASTnode>("-", MINUS, std::move(V), CurTok.lineNo);
    }
      case NOT: 
    {
      getNextToken(); // eat '!'
      auto V = ParseUnary();
      if (!V) {return LogError("Error in parsing binary expression.5");}
      return std::make_unique<UnaryASTnode>("!", NOT, std::move(V), CurTok.lineNo);
    }
      default: 
    {
      auto V = ParseRest();
      if (!V) {return LogError("Error in parsing binary expression.6");}
      return V;
    }
  }
}

static std::unique_ptr<ASTnode> ParseLocalDec(std::string type) {
  std::string VName;
  getNextToken(); //eat the type.

  if (CurTok.type != IDENT) {return LogError("Missing declaration identifier.");}
  VName = IdentifierStr;
  getNextToken();
  if (CurTok.type != SC) {return LogError("Missing ';'");}
  getNextToken(); // eat ';'
  
  return std::make_unique<VariableASTnode>(VName, type, CurTok.lineNo); // return variable declaration ASTnode.
}

static bool IsStatement() {
  int x = CurTok.type;
  if (x == RETURN || x == IF || x == WHILE || x == LBRA || x == NOT || x == MINUS || x == LPAR || x == IDENT
        || x == INT_LIT || x == FLOAT_LIT || x == BOOL_LIT || x == SC) {return true;}
  
  return false; 
}

static bool getE() {
  int x = CurTok.type;
  if (x == NOT || x == MINUS || x == LPAR || x == IDENT
        || x == INT_LIT || x == FLOAT_LIT || x == BOOL_LIT || x == SC) {return true;}
  
  return false; 
}

static std::unique_ptr<ASTnode> ParseExpression() { //TO DO LATER.
  std::string identifier = "";
  if (CurTok.type == IDENT) {
    identifier = IdentifierStr;
    TOKEN tok = peekToken(); //peak to the next token.
    if (tok.type != ASSIGN) { //if the next token is not a '='
      auto F = ParseUnary();
      auto X = ParseExpr(0, std::move(F));
      if (!X) {return LogError("Error while parsing binary expression.7");}
      return X;
      }
    getNextToken(); // eat IDENT
    getNextToken(); // eat '='
    auto V = ParseExpression(); //recursively parse.
    if (!V) {return LogError("Error while parsing expression.");}
    return std::make_unique<BinaryASTnode>("=", ASSIGN, std::make_unique<VariableReferenceASTnode>(identifier, CurTok.lineNo), std::move(V), CurTok.lineNo);
  } else {
    auto V = ParseUnary(); // parse the first unary.
    if (!V) {return LogError("Error while parsing binary expression.10");}
    auto X = ParseExpr(0, std::move(V));
    if (!X) {return LogError("Error while parsing binary expression.11");}
    return X;
  }
}

static std::unique_ptr<ASTnode> ParseExprStatement() { //CHECK WHAT THIS DOES.
  if (CurTok.type == SC) {getNextToken(); return std::unique_ptr<ASTnode>();} // if just ';' return nothing.
  auto V = ParseExpression();
  if (!V) {return LogError("Error while parsing binary expression.12");}
  if (CurTok.type != SC) {return LogError("Missing ';' after expression.");}
  getNextToken();
  return V;
}

static std::unique_ptr<ASTnode> ParseBody();
static std::unique_ptr<ASTnode> ParseIf() {
  getNextToken(); //eat 'if'
  if (CurTok.type != LPAR) {return LogError("Missing '(' in if statement definition.");}
  getNextToken(); // eat '('
  auto V = ParseExpression();
  if (!V) {return LogError("Error while parsing binary expression.13");}
  if (CurTok.type != RPAR) {return LogError("Missing ')' in if statement.");}
  getNextToken();
  auto X = ParseBody();

  if (CurTok.type == ELSE) {
    getNextToken(); // eat 'else'
    auto F = ParseBody(); // parse else body.
    return std::make_unique<IfASTnode>(std::move(V), std::move(X), std::move(F), true);
  }

  return std::make_unique<IfASTnode>(std::move(V), std::move(X), std::unique_ptr<ASTnode>(), false);
}

static std::unique_ptr<ASTnode> ParseAfterWhile();
static std::unique_ptr<ASTnode> ParseWhile () {
  getNextToken(); // eat 'while'
  if (CurTok.type != LPAR) {return LogError("Missing '(' in while loop.");}
  getNextToken(); //eat '('
  auto V = ParseExpression();
  if (!V) {return LogError("Error while parsing while loop.");}
  if (CurTok.type != RPAR) {return LogError("Missing ')' in while loop.");}
  getNextToken(); // eat ')'
  auto X = ParseAfterWhile();

  return std::make_unique<WhileASTnode>(std::move(V), std::move(X));
}


static std::unique_ptr<ASTnode> ParseAfterWhile() {
      switch(CurTok.type)
    { 
      case RETURN:
      {
        getNextToken(); //eat 'return'
        if (CurTok.type == SC) {
          //getNextToken(); 
          return std::make_unique<ReturnASTnode>(std::unique_ptr<ASTnode>(), false, CurTok.lineNo);
          } else {
          auto V = ParseUnary();
          if (!V) {return LogError("Error parsing binary expression.44");}
          auto X = ParseExpr(0, std::move(V));
          if (!X) {return LogError("Error paring binary expression.");}
          return std::make_unique<ReturnASTnode>(std::move(X), true, CurTok.lineNo);
        }
        if (CurTok.type != SC) {return LogError("Missing ';' after return statement");}
        getNextToken(); //eat ';'
        break;
      }
      case LBRA:
      {
        auto V = ParseBody(); //parse the the body: {.....}.
        if (!V) {return LogError("Error while parsing Body");}
        return V;
        break;
      }
      case IF:
      {
        auto V = ParseIf();
        if (!V) {return LogError("Error while parsing If statement.");}
        return V;
        break;
      }
      case WHILE:
      {
        auto V = ParseWhile();
        if (!V) {return LogError("Error while parsing While loop.");}
        return V;
        break;
      }
      default:
      {
        if (getE()) {
          auto V = ParseExprStatement();
          if (!V) {return LogError("Something went wrong.");}
          return V;
        } else {return LogError("Error, something invalid in function body.");} //Change this later.
      } 
    }
    return LogError("Error when parsing While statement body.");
}

static std::unique_ptr<ASTnode> ParseBody() {
  std::vector<std::unique_ptr<ASTnode>> Body;

  if (CurTok.type != LBRA) {return LogError("Missing '{'");}
  getNextToken(); // eat the '{'

  //loops over adding all the variable declarations if there are any.
  std::string VType = ParseType();
  while (VType.compare("error") != 0) {
    auto V = ParseLocalDec(VType);
    if (!V) {return nullptr;}
    Body.push_back(std::move(V));
    VType = ParseType(); // reset VType for next loop.
  }

  while (IsStatement()) {
    switch(CurTok.type)
    {
      case RETURN:
      {
        getNextToken(); //eat 'return'
        if (CurTok.type == SC) {
          //getNextToken(); 
          Body.push_back(std::make_unique<ReturnASTnode>(std::unique_ptr<ASTnode>(), false, CurTok.lineNo));
          } else {
          auto V = ParseUnary();
          if (!V) {return LogError("Error parsing binary expression.44");}
          auto X = ParseExpr(0, std::move(V));
          if (!X) {return LogError("Error paring binary expression.");}
          Body.push_back(std::make_unique<ReturnASTnode>(std::move(X), true, CurTok.lineNo));
        }
        if (CurTok.type != SC) {return LogError("Missing ';' after return statement");}
        getNextToken(); //eat ';'
        break;
      }
      case LBRA:
      {
        auto V = ParseBody(); //parse the the body: {.....}.
        if (!V) {return LogError("Error while parsing Body");}
        Body.push_back(std::move(V));
        break;
      }
      case IF:
      {
        auto V = ParseIf();
        if (!V) {return LogError("Error while parsing If statement.");}
        Body.push_back(std::move(V)); //MUST CHANGE LATER I THINIK.
        break;
      }
      case WHILE:
      {
        auto V = ParseWhile();
        if (!V) {return LogError("Error while parsing While loop.");}
        Body.push_back(std::move(V));
        break;
      }
      default:
      {
        if (getE()) {
          auto V = ParseExprStatement();
          if (!V) {return LogError("Something went wrong.");}
          Body.push_back(std::move(V));
        } else {return LogError("Error, something invalid in function body.");} //Change this later.
      } 
    }
  }

  if (CurTok.type != RBRA) {return LogError("Missing '}' at end of Body block.");}
  getNextToken(); // eat '}'

  return std::make_unique<BodyASTnode>(std::move(Body));
}

static std::unique_ptr<ASTnode> Parsedecl() {
  std::string FnName; 
  std::string FnType = ParseType(); // get the function type.

  if (FnType.compare("error") == 0) {LogError("Expected function type declaration"); return nullptr;} //throw error if incrorect.
  getNextToken(); // eat type.

  if (CurTok.type != IDENT)
    return LogError("Expected Identifier.");

  FnName = IdentifierStr;
  getNextToken(); // eat tok_identifier

  if (CurTok.type == SC && FnType.compare("void") != 0) { //parse a simple variable declaration.
    getNextToken(); //eat the ';'
    return std::make_unique<VariableASTnode>(FnName, FnType, CurTok.lineNo); // return variable declaration ASTnode.
  } else if (CurTok.type == LPAR) { //parse a function declaration.
    auto V = ParsePrototype(FnType, FnName); // parse the prototype fully.
    std::unique_ptr<ASTnode> X = ParseBody();
    return std::make_unique<FunctionASTnode>(std::move(V), std::move(X));
  } else { //some kind of error has occured.
    return LogError("Invalid function or variable declaration.");
  }

}

static std::vector<std::unique_ptr<ASTnode>> ParseDec() {
  std::vector<std::unique_ptr<ASTnode>> DecList;
  
  auto V = Parsedecl();

  if(!V) {return std::vector<std::unique_ptr<ASTnode>>();} //exit program if error found.

  DecList.push_back(std::move(V)); // ad the delcaration to the list.

  std::string dec = ParseType();
  while (dec.compare("error") != 0) {
    V = Parsedecl();
    if (!V) {return std::vector<std::unique_ptr<ASTnode>>();}
    DecList.push_back(std::move(V));
    V.reset();
    dec = ParseType();
  }

  return DecList;
}

// program ::= extern_list decl_list
static ProgASTnode parser() {
 std::string Type = ParseType(); //get the type.
 int f = 0;
 if (Type.compare("error") != 0) {f = 1;} //set flag to 1;

  while(true) {
    fprintf(stderr, "ready> ");
    switch(CurTok.type) {

      
      case EXTERN: 
      {
        std::vector<std::unique_ptr<ProtoAST>> V = ParseExtern();
        std::vector<std::unique_ptr<ASTnode>>  X = ParseDec();
        if (V.size() == 0 || X.size() == 0) {return ProgASTnode(std::vector<std::unique_ptr<ProtoAST>>(), std::vector<std::unique_ptr<ASTnode>>());}
        if (CurTok.type != EOF_TOK) {return ProgASTnode(std::vector<std::unique_ptr<ProtoAST>>(), std::vector<std::unique_ptr<ASTnode>>());}
        return ProgASTnode(std::move(V), std::move(X));
      }
      default:
      {
        if (f == 1) {
          std::vector<std::unique_ptr<ASTnode>>  X = ParseDec();
          if (X.size() == 0) {return ProgASTnode(std::vector<std::unique_ptr<ProtoAST>>(), std::vector<std::unique_ptr<ASTnode>>());}
          if (CurTok.type != EOF_TOK) {return ProgASTnode(std::vector<std::unique_ptr<ProtoAST>>(), std::vector<std::unique_ptr<ASTnode>>());}
          return ProgASTnode(std::vector<std::unique_ptr<ProtoAST>>(), std::move(X));
        }

        fprintf(stderr, "Error: couldn't find a valid function declaration.\n"); // print error for no function definitions.
        return ProgASTnode(std::vector<std::unique_ptr<ProtoAST>>(), std::vector<std::unique_ptr<ASTnode>>()); //return a empty vector; 
      }  
    }
  }
}

//TESTING TIME.

/// FloatASTnode - Class for integer literals like 1, 2, 10,
class TestASTnode : public ASTnode {
  std::unique_ptr<ASTnode> P;
public: 
  TestASTnode(std::unique_ptr<ASTnode> p) : P(std::move(p)) {}
  virtual Value *codegen() override;
  virtual std::string to_string(int depth) const override {
      return P->to_string(0);
  };
};



static TestASTnode test() {
  auto V = Parsedecl();
  return TestASTnode(std::move(V));
}

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::map<std::string, AllocaInst *> NamedValues;
static std::map<std::string, AllocaInst *> OldValues; //stores the old casting of values to set them after scope.
static std::map<std::string, std::string> ReDefined;
static std::map<std::string, GlobalVariable *> GlobalValues;
static std::map<std::string, std::string> DefinedValues;
static std::map<std::string, std::string> VarTypes;
static std::map<std::string, std::string> GlobalVarTypes;
static std::unique_ptr<Module> TheModule;
static Type *FuncType;
static bool RetCheck = false;

bool codecheck = true;

Value *LogErrorV(const char *Str, int number) {
  if (codecheck) {fprintf(stderr, "Error: %s At line number: %d\n", Str, number); codecheck = false;}
  return nullptr;
}

Function *LogErrorF(const char *Str) {
  if (codecheck) {fprintf(stderr, "Error: %s\n", Str); codecheck = false;}
  return nullptr;
}

static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction, Type *ty, const std::string &VarName) {
  IRBuilder<> TmpB(&TheFunction->getEntryBlock(), TheFunction->getEntryBlock().begin());

  return TmpB.CreateAlloca(ty, 0,VarName.c_str());
}

//FUNCTION CODEGEN():

Function *ProtoAST::codegen() {
  std::vector<Type *> varTypes;

  for (auto & i : Types) { //iterate over the parameters adding types to the Types vector.
    if (i.compare("Int") == 0) {
      varTypes.push_back(Type::getInt32Ty(TheContext));
    } else if (i.compare("Float") == 0) {
      varTypes.push_back(Type::getFloatTy(TheContext));
    } else if (i.compare("bool") == 0) {
      varTypes.push_back(Type::getInt1Ty(TheContext));
    }
  }

  FunctionType *FT;

  if (Identifier.compare("Int") == 0) {
    FT = FunctionType::get(Type::getInt32Ty(TheContext), varTypes, false);
  } else if (Identifier.compare("Float") == 0) {
    FT = FunctionType::get(Type::getFloatTy(TheContext), varTypes, false);
  } else if (Identifier.compare("bool") == 0) {
    FT = FunctionType::get(Type::getInt1Ty(TheContext), varTypes, false);
  } else if (Identifier.compare("void") == 0) {
    FT = FunctionType::get(Type::getVoidTy(TheContext), varTypes, false);
  }

  Function *F = Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());

  unsigned Idx = 0;
  for (auto &Arg : F->args())
    Arg.setName(Params[Idx++]);

  return F;
}

Function *FunctionASTnode::codegen() {
  Function *TheFunction = TheModule->getFunction(Proto->getName());

  if (!TheFunction)
    TheFunction = Proto->codegen();

  if (!TheFunction)
    return LogErrorF("Error loading function prototype");
  
  BasicBlock *BB = BasicBlock::Create(TheContext, "entry", TheFunction);
  Builder.SetInsertPoint(BB);

  NamedValues.clear();
  DefinedValues.clear();
  for (auto &Arg : TheFunction->args()) {
    AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, Arg.getType(), Arg.getName().str());
    Builder.CreateStore(&Arg, Alloca);
    NamedValues[std::string(Arg.getName())] = Alloca;
  }

  RetCheck = false;
  FuncType = TheFunction->getReturnType();
  Value *RetVal = Body->codegen();
  if (FuncType == Type::getVoidTy(TheContext)) {
    Builder.CreateRetVoid(); //create a void return type.
  }
  if (RetCheck == false) {
    return LogErrorF("Missing return statement in function.");
  }

  //if (Value *RetVal = Body->codegen()) {
    //Builder.CreateRet(RetVal);
  
  verifyFunction(*TheFunction);

  return TheFunction;
  //}

  TheFunction->eraseFromParent();
  return nullptr;
}

Value *CalleeASTnode::codegen() {
  Function *CalleeF = TheModule->getFunction(Name);
  if (!CalleeF)
    return LogErrorV("Unknown function referenced.", lineNumber);
  
  if (CalleeF->arg_size() != Args.size())
    return LogErrorV("Incorrect number of arguments passed.", lineNumber);
  
  std::vector<Value *> ArgsV;
  for (unsigned i = 0, e = Args.size(); i != e; ++i) {
    ArgsV.push_back(Args[i]->codegen());
    if (!ArgsV.back())
      return nullptr;
  }

  return Builder.CreateCall(CalleeF, ArgsV, "calltmp");
}

Value *IntASTnode::codegen() {
  return ConstantInt::get(TheContext, APInt(32, Val, true));
}

Value *FloatASTnode::codegen() {
  return ConstantFP::get(TheContext, APFloat(Val));
}

Value *BoolASTnode::codegen() {
  if (Val) {return ConstantInt::get(TheContext, APInt(1, Val, false));} else {return ConstantInt::get(TheContext, APInt(1, Val, false));}
}

Value *VariableReferenceASTnode::codegen() {
  AllocaInst *V = NamedValues[Name];
  GlobalVariable *GV = GlobalValues[Name];
  if (!V && !GV) {return LogErrorV("Unknown variable referenced.", lineNumber);}
  std::string check = DefinedValues[Name].c_str();
  if (check.compare("UNDEFINED") == 0) {LogErrorV("Reference to an undefined variable.", lineNumber);} //CONSIDER ADDING AN EXIT AFTER AN ERROR.

  if (!GV) {
    Type *T = V->getAllocatedType();
    if (T == Type::getInt32Ty(TheContext)) {
      return Builder.CreateLoad(Type::getInt32Ty(TheContext), V, Name.c_str());
    } else if (T == Type::getInt1Ty(TheContext)) {
      return Builder.CreateLoad(Type::getInt1Ty(TheContext), V, Name.c_str());
    } else if (T == Type::getFloatTy(TheContext)) {
      return Builder.CreateLoad(Type::getFloatTy(TheContext), V, Name.c_str());
    }
  } else { //DO THE SAME FOR GLOBAL VARIABLES.
    Type *T = GV->getValueType();
    if (T == Type::getInt32Ty(TheContext)) {
      return Builder.CreateLoad(Type::getInt32Ty(TheContext), GV, Name.c_str());
    } else if (T == Type::getInt1Ty(TheContext)) {
      return Builder.CreateLoad(Type::getInt1Ty(TheContext), GV, Name.c_str());
    } else if (T == Type::getFloatTy(TheContext)) {
      return Builder.CreateLoad(Type::getFloatTy(TheContext), GV, Name.c_str());
    }
  }
}

Value *VariableASTnode::codegen() {
  Function* TheFunction = Builder.GetInsertBlock()->getParent();

  if (Type.compare("Int") == 0) {

    AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, Type::getInt32Ty(TheContext), Name);

    Builder.CreateStore(ConstantInt::get(TheContext, APInt(32, 0, false)), Alloca); //set the variable with a starting value of null.

    NamedValues[Name] = Alloca;
    DefinedValues[Name] = "UNDEFINED";
    return nullptr;
  } else if (Type.compare("Float") == 0) {
    AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, Type::getFloatTy(TheContext), Name);

    float val = 0.0;
    Builder.CreateStore(ConstantFP::get(TheContext, APFloat(val)), Alloca); //set the variable with a starting value of null.

    NamedValues[Name] = Alloca;
    DefinedValues[Name] = "UNDEFINED";
    return nullptr;
  } else if (Type.compare("bool") == 0) { //FINISH THIS LATER.
    AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, Type::getInt1Ty(TheContext), Name);

    Builder.CreateStore(ConstantInt::get(TheContext, APInt(1, 0, false)), Alloca); //set the variable with a starting value of null.

    NamedValues[Name] = Alloca;
    DefinedValues[Name] = "UNDEFINED";
    return nullptr;
  }

  return LogErrorV("Missing or unknown variable type.", lineNumber);
}

Value *UnaryASTnode::codegen() {
    Value *Unary = Next->codegen();
    Type *UType = Unary->getType();

    if (!Unary)
      return nullptr;
  
    if (UType->isFloatingPointTy()) {
      switch(intType) {
        case MINUS:
        {
          Unary = Builder.CreateFNeg(Unary, "negtmp");
          return Unary;
        }
        case NOT:
        {
          Unary = Builder.CreateFPToUI(Unary, Type::getInt1Ty(TheContext), "intcast"); 
          Unary = Builder.CreateNot(Unary, "nottmp");
          return Unary;
        }
      }
    } else if (UType->isIntegerTy()) {
      switch(intType) {
        case MINUS:
        {
          Unary = Builder.CreateNeg(Unary, "negtmp");
          return Unary;
        }
        case NOT:
        { 
          Unary = Builder.CreateNot(Unary, "nottmp");
          return Unary;
        }
      }
    }
  
  return LogErrorV("Failure to codegen the a unary expression.", lineNumber);
}

Value *BinaryASTnode::codegen() { //CONSIDER ADDING FUNCTIONALITY FOR TYPE CASTING E.G. INT A = 2.0 ETC.
    if (intType == ASSIGN) { // special case for assignments.

      VariableReferenceASTnode *LHSE = static_cast<VariableReferenceASTnode *>(LHS.get());

    if (!LHSE)
      return LogErrorV("destination of '=' must be a variable", lineNumber);

    Value *Val = RHS->codegen();
    if (!Val)
      return nullptr;
    
    AllocaInst *Variable = NamedValues[LHSE->getName()];
    GlobalVariable* global = GlobalValues[LHSE->getName()];  
    if (!Variable && !global)
      return LogErrorV("Unknown variable name", lineNumber);
    
    if (!global) {
      Type *VType = Val->getType();
      Type *AType = Variable->getAllocatedType();
      if (VType->isFloatingPointTy() && AType->isIntegerTy()) {
        Val = Builder.CreateFPToUI(Val, Type::getInt32Ty(TheContext), "intcast");
      } else if (VType->isIntegerTy() && AType->isFloatingPointTy()) {
        Val = Builder.CreateSIToFP(Val, Type::getFloatTy(TheContext), "floatcast");
      }
      Builder.CreateStore(Val, Variable);
    } else {
      Type *VType = Val->getType();
      Type *AType = global->getValueType();
      if (VType->isFloatingPointTy() && AType->isIntegerTy()) {
        Val = Builder.CreateFPToUI(Val, Type::getInt32Ty(TheContext), "intcast");
      } else if (VType->isIntegerTy() && AType->isFloatingPointTy()) {
        Val = Builder.CreateSIToFP(Val, Type::getFloatTy(TheContext), "floatcast");
      }
      Builder.CreateStore(Val, global);
    }

    DefinedValues[LHSE->getName()] = "DEFINED";
    return Val;
    }

    Value *L = LHS->codegen();
    Value *R = RHS->codegen();

    if (!L || !R)
      return nullptr;

    Type *LType = L->getType();
    Type *RType = R->getType();

    // if (intType == PLUS || intType ==  MINUS || intType == ASTERIX || intType == DIV || intType == MOD) {
    //   if (LType == Type::getInt1Ty(TheContext) && RType == Type::getInt32Ty(TheContext)) {
    //     L = Builder.CreateIntCast(L, Type::getInt32Ty(TheContext), true, "boolcast");
    //   } else if (RType == Type::getInt1Ty(TheContext) && LType == Type::getInt32Ty(TheContext)) {
    //     R = Builder.CreateIntCast(R, Type::getInt32Ty(TheContext), true "boolcast");
    //   }
    // }

    if (LType->isFloatingPointTy() && RType->isIntegerTy()) {
      R = Builder.CreateSIToFP(R, Type::getFloatTy(TheContext), "floatcast");
    } else if (LType->isIntegerTy() && RType->isFloatingPointTy()) {
      L = Builder.CreateSIToFP(L, Type::getFloatTy(TheContext), "floatcast");
    }
    
    LType = L->getType();
    RType = R->getType();

    if (LType->isFloatingPointTy() && RType->isFloatingPointTy()) {
      switch (intType) {
        case PLUS:
          return Builder.CreateFAdd(L, R, "addtmp");
        case MINUS:
          return Builder.CreateFSub(L, R, "subtmp");
        case ASTERIX:
          return Builder.CreateFMul(L, R, "multmp");
        case DIV:
          return Builder.CreateFDiv(L, R, "divtmp");
        case MOD:
          return Builder.CreateFRem(L, R, "modtmp");
        case OR:
          return Builder.CreateOr(L, R, "ortmp");
        case AND:
          return Builder.CreateAnd(L, R, "andtmp");
        case EQ:
        {
          L = Builder.CreateFCmpUEQ(L, R, "eqtmp");
          return Builder.CreateUIToFP(L, Type::getInt1Ty(TheContext), "booltmp");
        }
        case NE:
        {
          L = Builder.CreateFCmpUNE(L, R, "netmp");
          return Builder.CreateUIToFP(L, Type::getInt1Ty(TheContext), "booltmp");
        }
        case LE:
        {
          L = Builder.CreateFCmpULE(L, R, "letmp");
          return Builder.CreateUIToFP(L, Type::getInt1Ty(TheContext), "booltmp");
        }
        case LT:
        {
          L = Builder.CreateFCmpULT(L, R, "lttmp");
          return Builder.CreateUIToFP(L, Type::getInt1Ty(TheContext), "booltmp");
        }
        case GE:
        {
          L = Builder.CreateFCmpUGE(L, R, "getmp");
          return Builder.CreateUIToFP(L, Type::getInt1Ty(TheContext), "booltmp");
        }
        case GT:
        {
          L = Builder.CreateFCmpUGT(L, R, "gttmp");
          return Builder.CreateUIToFP(L, Type::getInt1Ty(TheContext), "booltmp");
        }
        default:
          return LogErrorV("invalid binary operator", lineNumber);
      } 

    }  
    if (LType->isIntegerTy() && RType->isIntegerTy()) {
      switch (intType) {
        case PLUS:
          return Builder.CreateAdd(R, L, "addtmp");
        case MINUS:
          return Builder.CreateSub(L, R, "subtmp");
        case ASTERIX:
          return Builder.CreateMul(L, R, "multmp");
        case DIV:
          return Builder.CreateSDiv(L, R, "divtmp");
        case MOD:
          return Builder.CreateSRem(L, R, "modtmp");
        case OR:
          return Builder.CreateOr(L, R, "ortmp");
        case AND:
          return Builder.CreateAnd(L, R, "andtmp");
        case EQ:
        {
          L = Builder.CreateICmpEQ(L, R, "eqtmp");
          return Builder.CreateUIToFP(L, Type::getInt1Ty(TheContext), "booltmp");
        }
        case NE:
        {
          L = Builder.CreateICmpNE(L, R, "netmp");
          return Builder.CreateUIToFP(L, Type::getInt1Ty(TheContext), "booltmp");
        }
        case LE:
        {
          L = Builder.CreateICmpULE(L, R, "letmp");
          return Builder.CreateUIToFP(L, Type::getInt1Ty(TheContext), "booltmp");
        }
        case LT:
        {
          L = Builder.CreateICmpULT(L, R, "lttmp");
          return Builder.CreateUIToFP(L, Type::getInt1Ty(TheContext), "booltmp");
        }
        case GE:
        {
          L = Builder.CreateICmpUGE(L, R, "getmp");
          return Builder.CreateUIToFP(L, Type::getInt1Ty(TheContext), "booltmp");
        }
        case GT:
        {
          L = Builder.CreateICmpUGT(L, R, "gttmp");
          return Builder.CreateUIToFP(L, Type::getInt1Ty(TheContext), "booltmp");
        }
        default:
          return LogErrorV("invalid binary operator", lineNumber);
      }         
    }

    return LogErrorV("Error, mismatching types.", lineNumber);  
}

Value *ReturnASTnode::codegen() { //MUST CHANGE TO TYPE CAST RETURN VALEUS OF INT TO FLOAT AND FLOAT TO INT.
  RetCheck = true; //set the return to true.
  if (Flag) {
    Value *V = Bin->codegen();
    if (!V)
      return LogErrorV("int Function return statement", lineNumber);
    if (V->getType() != FuncType) {return LogErrorV("Return type does not match function type.", lineNumber);}
    Builder.CreateRet(V); //create a non void return type.
  } else {
    if (!FuncType->isVoidTy()) {return LogErrorV("Return type does not match function type.", lineNumber);}
    Builder.CreateRetVoid(); //create a void return type.
  }
  return nullptr;
}

Value *WhileASTnode::codegen() {
  Function *TheFunction = Builder.GetInsertBlock()->getParent();

  BasicBlock *CondBB = BasicBlock::Create(TheContext, "Condition", TheFunction);
  BasicBlock *LoopBB = BasicBlock::Create(TheContext, "loop");
  BasicBlock *EndBB = BasicBlock::Create(TheContext, "whilecont");

  Builder.CreateBr(CondBB);
  Builder.SetInsertPoint(CondBB);

  Value *CondV = Exp->codegen();
  Type *CondVT = CondV->getType();
  if (!CondV)
    return nullptr;

  if (CondVT->isFloatingPointTy()) {
    CondV = Builder.CreateFCmpUNE(CondV, ConstantFP::get(TheContext, APFloat(0.0)));
  } else {
    if (CondVT == Type::getInt1Ty(TheContext)) {
      CondV = Builder.CreateICmpNE(CondV, ConstantInt::get(TheContext, APInt(1, 0)));
    } else {
      CondV = Builder.CreateICmpNE(CondV, ConstantInt::get(TheContext, APInt(32, 0)));
    }
  }
  
  Builder.CreateCondBr(CondV, LoopBB, EndBB);
  TheFunction->getBasicBlockList().push_back(LoopBB);
  Builder.SetInsertPoint(LoopBB);

  Value *LBody = Body->codegen(); //codegen the body.

  Builder.CreateBr(CondBB);

  TheFunction->getBasicBlockList().push_back(EndBB);
  Builder.SetInsertPoint(EndBB);

  return nullptr;
}


Value *IfASTnode::codegen() {
  Function *TheFunction = Builder.GetInsertBlock()->getParent();
  BasicBlock* _true = BasicBlock::Create(TheContext, "then", TheFunction);
  BasicBlock* _else = BasicBlock::Create(TheContext, "else");
  BasicBlock* Rest = BasicBlock::Create(TheContext, "ifcont");

  Value *CondV = Exp->codegen();
  Type *CondVT = CondV->getType();
  if (!CondV) {return nullptr;}

  if (CondVT->isFloatingPointTy()) {
    CondV = Builder.CreateFCmpUNE(CondV, ConstantFP::get(TheContext, APFloat(0.0)));
  } else {
    if (CondVT == Type::getInt1Ty(TheContext)) {
      CondV = Builder.CreateICmpNE(CondV, ConstantInt::get(TheContext, APInt(1, 0)));
    } else {
      CondV = Builder.CreateICmpNE(CondV, ConstantInt::get(TheContext, APInt(32, 0)));
    }
  }
  
  if (Flag) { // if there is a else statement.
    Builder.CreateCondBr(CondV, _true, _else);
    Builder.SetInsertPoint(_true);

    Value *IfBody = Body->codegen();


    Builder.CreateBr(Rest);


    TheFunction->getBasicBlockList().push_back(_else);
    Builder.SetInsertPoint(_else);


    Value *Else = EBody->codegen();

    Builder.CreateBr(Rest);

    TheFunction->getBasicBlockList().push_back(Rest);
    Builder.SetInsertPoint(Rest);
  } else { // if there isn't a else statement
    Builder.CreateCondBr(CondV, _true, Rest);
    Builder.SetInsertPoint(_true);

    Value *IfBody = Body->codegen();


    Builder.CreateBr(Rest);
    TheFunction->getBasicBlockList().push_back(Rest);
    Builder.SetInsertPoint(Rest);
  }

  return  nullptr;
}

Value *BodyASTnode::codegen() {
  for (auto & i : Content) {
    i->codegen();
  }

  return  nullptr;
}

Value *ProgASTnode::codegen() {
  for (auto & i : ExternList) {
    auto *F = i->codegen();
    if (!F)
      return nullptr;
    //F->print(errs()); fprintf(stderr, "\n");
  }

  for (auto & i : DecList) {
    if (i->isVariable()) {
      VariableASTnode *node = static_cast<VariableASTnode *>(i.get());
      if (GlobalValues[node->getName()])
        return LogErrorV("Refinitions of global variables are not allowed.", node->getLineNumber());
      Type *type = Type::getFloatTy(TheContext);
      std::string T = node->getType();
      if (T.compare("Int") == 0) {
        type = Type::getInt32Ty(TheContext);
      } else if (T.compare("Float") == 0) {
        type = Type::getFloatTy(TheContext);
      } else if (T.compare("bool") == 0) { //FINISH THIS LATER.
        type = Type::getInt1Ty(TheContext);
      }
      GlobalVariable* g = new GlobalVariable(*TheModule, type, false, GlobalValue::CommonLinkage, Constant::getNullValue(type)); //create a new global.
      GlobalValues[i->getName()] = g;
      DefinedValues[i->getName()] = "UNDEFINED";
      //g->print(errs()); fprintf(stderr, "\n");
      //fprintf(stderr, "\n");
    } else {
      auto *F = i->codegen();
        if (!F)
          return nullptr;
      //F->print(errs()); fprintf(stderr, "\n");
    }
  }
  Value *returnValue;
  return returnValue;
}

Value *TestASTnode::codegen() {
  return P->codegen();
}

//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
                                     const ASTnode &ast) {
  os << ast.to_string(0);
  return os;
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main(int argc, char **argv) {
  if (argc == 2) {
    pFile = fopen(argv[1], "r");
    if (pFile == NULL)
      perror("Error opening file");
  } else {
    std::cout << "Usage: ./code InputFile\n";
    return 1;
  }

  // initialize line number and column numbers to zero
  lineNo = 1;
  columnNo = 1;

  // get the first token
 //getNextToken();
  //while (CurTok.type != EOF_TOK) {
    //fprintf(stderr, "Token: %s with type %d\n", CurTok.lexeme.c_str(),
            //CurTok.type);
    //getNextToken();
  //}
  //fprintf(stderr, "Lexer Finished\n");

  // Make the module, which holds all the code.
  TheModule = std::make_unique<Module>("mini-c", TheContext);

  // Install standard binary operators.
  // 1 is lowest precedence.
  BinopPrecedence[OR] = 10;
  BinopPrecedence[AND] = 20;
  BinopPrecedence[EQ] = 30;
  BinopPrecedence[NE] = 30;
  BinopPrecedence[LE] = 40;
  BinopPrecedence[LT] = 40;
  BinopPrecedence[GE] = 40;
  BinopPrecedence[GT] = 40;
  BinopPrecedence[PLUS] = 50;
  BinopPrecedence[MINUS] = 50;
  BinopPrecedence[ASTERIX] = 60; // highest.
  BinopPrecedence[DIV] = 60; // highest
  BinopPrecedence[MOD] = 60; // highest

  // Run the parser now.
  getNextToken();
  auto Root = parser();
  //auto Root = test();
  fprintf(stderr, "Parsing Finished\n");

  //UNCOMENT LATER. TO BE USED.
  if (!Root.IsEmpty() && check) {llvm::outs() << Root << "\n";}
  if (check && codecheck) {Root.codegen();}

  //********************* Start printing final IR **************************
  // Print out all of the generated code into a file called output.ll
  auto Filename = "output.ll";
  std::error_code EC;
  raw_fd_ostream dest(Filename, EC, sys::fs::OF_None);

  if (EC) {
    errs() << "Could not open file: " << EC.message();
    return 1;
  }
  //TheModule->print(errs(), nullptr); // print IR to terminal
  TheModule->print(dest, nullptr);
  //********************* End printing final IR ****************************

  fclose(pFile); // close the file that contains the code that was parsed
  return 0;
}
