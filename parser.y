%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "header.h"
#include "symtab.h"
#include "semcheck.h"

extern int linenum;
extern FILE	*yyin;
extern char	*yytext;
extern char buf[256];
extern int Opt_Symbol;		/* declared in lex.l */
extern FILE *output; /*declared in main.c*/

int scope = 0;
int nextLocalVarNum;
int boolLabelNum;
struct PTypeList *currentFuncCallParam;
SEMTYPE currentDeclType;
int isMain;
int ifLabelNum = 0;
int loopLabelNum = 0;
//int currentLoopNum = -1;
struct loopStackNode *loopStackTop;

char fileName[256];
struct SymTable *symbolTable;
__BOOLEAN paramError;
struct PType *funcReturn;
__BOOLEAN semError = __FALSE;
int inloop = 0;

//void breakpoint(){};

void pushLoopStack(int num){
	
	struct loopStackNode *tmp = (struct loopStackNode*)malloc(sizeof(struct loopStackNode));
	tmp->loopNum = num;
	tmp->previous = loopStackTop;
	loopStackTop = tmp;
	
}

int popLoopStack(){
	int tmp = loopStackTop->loopNum;
	loopStackTop = loopStackTop->previous;
	return tmp;
}

char type2char(SEMTYPE type){
	switch(type){
		case INTEGER_t:
			return 'I';
			break;
		case FLOAT_t:
			return 'F';
			break;
		case DOUBLE_t:
			return 'D';
			break;
		case BOOLEAN_t:
			return 'Z';
			break;
		case STRING_t:
			return 'S';
			break;
	}
	return 'V';
}

char loadType(char c){
	switch (c) {
		case 'I': return 'i';
		case 'Z': return 'i';
		case 'D': return 'd';
		case 'F': return 'f';
	}
	return 'v';
}

void ifdCast(SEMTYPE ltype, SEMTYPE rtype, int nextVarNum){
	//stack: l r (top)
	if(ltype < rtype){//cast l
		//store r to nextVarNum
		fprintf(output, "%cstore %d\n", loadType(type2char(rtype)),nextVarNum);
		//stack: l (top)
		fprintf(output, "%c2%c\n", loadType(type2char(ltype)), loadType(type2char(rtype)));
		//push r back
		fprintf(output, "%cload %d\n", loadType(type2char(rtype)),nextVarNum);
	}
	else if(ltype > rtype){//cast r
		fprintf(output, "%c2%c\n", loadType(type2char(rtype)), loadType(type2char(ltype)));
	}	
	
}
%}

%union {
	int intVal;
	float floatVal;	
	char *lexeme;
	struct idNode_sem *id;
	struct ConstAttr *constVal;
	struct PType *ptype;
	struct param_sem *par;
	struct expr_sem *exprs;
	struct expr_sem_node *exprNode;
	struct constParam *constNode;
	struct varDeclParam* varDeclNode;
};

%token	LE_OP NE_OP GE_OP EQ_OP AND_OP OR_OP
%token	READ BOOLEAN WHILE DO IF ELSE TRUE FALSE FOR INT PRINT BOOL VOID FLOAT DOUBLE STRING CONTINUE BREAK RETURN CONST
%token	L_PAREN R_PAREN COMMA SEMICOLON ML_BRACE MR_BRACE L_BRACE R_BRACE ADD_OP SUB_OP MUL_OP DIV_OP MOD_OP ASSIGN_OP LT_OP GT_OP NOT_OP

%token <lexeme>ID
%token <intVal>INT_CONST 
%token <floatVal>FLOAT_CONST
%token <floatVal>SCIENTIFIC
%token <lexeme>STR_CONST

%type<ptype> scalar_type dim
%type<par> array_decl parameter_list
%type<constVal> literal_const
%type<constNode> const_list 
%type<exprs> variable_reference logical_expression logical_term logical_factor relation_expression arithmetic_expression term factor logical_expression_list literal_list initial_array
%type<intVal> relation_operator add_op mul_op dimension
%type<varDeclNode> identifier_list
%type<intVal> GenerateIFLabel GenerateLoopLabel GenerateForLabel

%start program
%%

program :	{
				/*
				.class public output
				.super java/lang/Object
				*/
				fprintf(output, ".class public output\n.super java/lang/Object\n");
				fprintf(output, ".field public static _sc Ljava/util/Scanner;\n");
				loopStackTop = (struct loopStackNode*)malloc(sizeof(struct loopStackNode));
				loopStackTop->previous = 0;
			}
				decl_list 
			    funct_def
				decl_and_def_list 
				{
					checkUndefinedFunc(symbolTable);
					if(Opt_Symbol == 1)
					printSymTable( symbolTable, scope );	
				}
		;

decl_list : decl_list var_decl
		  | decl_list const_decl
		  | decl_list funct_decl
		  |
		  ;


decl_and_def_list : decl_and_def_list var_decl
				  | decl_and_def_list const_decl
				  | decl_and_def_list funct_decl
				  | decl_and_def_list funct_def
				  | 
				  ;

		  
funct_def : scalar_type ID L_PAREN R_PAREN 
			{
				funcReturn = $1; 
				struct SymNode *node;
				node = findFuncDeclaration( symbolTable, $2 );
				
				if( node != 0 ){
					verifyFuncDeclaration( symbolTable, 0, $1, node );
				}
				else{
					insertFuncIntoSymTable( symbolTable, $2, 0, $1, scope, __TRUE );
				}
				
				if(strcmp($2,"main")==0){
					fprintf(output, ".method public static main([Ljava/lang/String;)V\n");
					fprintf(output, ".limit stack 100\n.limit locals 100\n");
					fprintf(output, "new java/util/Scanner\n");
					fprintf(output, "dup\n");
					fprintf(output, "getstatic java/lang/System/in Ljava/io/InputStream;\n");
					fprintf(output, "invokespecial java/util/Scanner/<init>(Ljava/io/InputStream;)V\n");
					fprintf(output, "putstatic output/_sc Ljava/util/Scanner;\n");
				}
				else{
					fprintf(output, ".method public static %s()%c\n", $2, type2char($1->type));
					
					fprintf(output, ".limit stack 100\n.limit locals 100\n");
					
				}
				
				boolLabelNum=0;
				//set the next local var stack #
				if(strcmp($2,"main")==0){
					isMain=1;
					nextLocalVarNum=1;
				}
				else{
					isMain=0;
					nextLocalVarNum=0;
				}
			}
			compound_statement { funcReturn = 0; if(isMain){fprintf(output, "return\n");}fprintf(output, ".end method\n");}	
		  | scalar_type ID L_PAREN parameter_list R_PAREN  
			{				
				funcReturn = $1;
				
				boolLabelNum=0;
				//set the next local var stack #
				if(strcmp($2,"main")==0){
					isMain=1;
					nextLocalVarNum=1;
				}
				else{
					isMain=0;
					nextLocalVarNum=0;
				}
				
				if(strcmp($2,"main")==0){
					fprintf(output, ".method public static main([Ljava/lang/String;)V\n");
					fprintf(output, ".limit stack 100\n.limit locals 100\n");
					fprintf(output, "new java/util/Scanner\n");
					fprintf(output, "dup\n");
					fprintf(output, "getstatic java/lang/System/in Ljava/io/InputStream;\n");
					fprintf(output, "invokespecial java/util/Scanner/<init>(Ljava/io/InputStream;)V\n");
					fprintf(output, "putstatic output/_sc Ljava/util/Scanner;\n");
				}
				else{
					fprintf(output, ".method public static %s(", $2);
					
					//params
					struct param_sem *parPtr;
					for( parPtr=$4 ; parPtr!=0 ; parPtr=(parPtr->next) ) {
						if(parPtr->pType->isError == __TRUE)continue;
						
						fprintf(output, "%c", type2char(parPtr->pType->type));
						
					}
					
					fprintf(output, ")%c\n.limit stack 100\n.limit locals 100\n", type2char($1->type));
					
				}
				
				paramError = checkFuncParam( $4 );
				if( paramError == __TRUE ){
					fprintf( stdout, "########## Error at Line#%d: param(s) with several fault!! ##########\n", linenum );
					semError = __TRUE;
				}
				
				// check and insert function into symbol table
				else{
					struct SymNode *node;
					node = findFuncDeclaration( symbolTable, $2 );

					if( node != 0 ){
						if(verifyFuncDeclaration( symbolTable, $4, $1, node ) == __TRUE){	
							insertParamIntoSymTable( symbolTable, $4, scope+1, &nextLocalVarNum );
						}				
					}
					else{
						insertParamIntoSymTable( symbolTable, $4, scope+1, &nextLocalVarNum );				
						insertFuncIntoSymTable( symbolTable, $2, $4, $1, scope, __TRUE );
					}
				}
			} 	
			compound_statement { funcReturn = 0; if(isMain){fprintf(output, "return\n");} fprintf(output, ".end method\n");}
		  | VOID ID L_PAREN R_PAREN 
			{
				funcReturn = createPType(VOID_t); 
				struct SymNode *node;
				node = findFuncDeclaration( symbolTable, $2 );

				if( node != 0 ){
					verifyFuncDeclaration( symbolTable, 0, createPType( VOID_t ), node );					
				}
				else{
					insertFuncIntoSymTable( symbolTable, $2, 0, createPType( VOID_t ), scope, __TRUE );	
				}
				
				if(strcmp($2,"main")==0){
					fprintf(output, ".method public static main([Ljava/lang/String;)V\n");
					fprintf(output, ".limit stack 100\n.limit locals 100\n");
					fprintf(output, "new java/util/Scanner\n");
					fprintf(output, "dup\n");
					fprintf(output, "getstatic java/lang/System/in Ljava/io/InputStream;\n");
					fprintf(output, "invokespecial java/util/Scanner/<init>(Ljava/io/InputStream;)V\n");
					fprintf(output, "putstatic output/_sc Ljava/util/Scanner;\n");
				}
				else{
					fprintf(output, ".method public static %s()V\n.limit stack 100\n.limit locals 100\n", $2);
				}
				
				boolLabelNum=0;
				//set the next local var stack #
				if(strcmp($2,"main")==0){
					isMain=1;
					nextLocalVarNum=1;
				}
				else{
					isMain=0;
					nextLocalVarNum=0;
				}
			}
			compound_statement { funcReturn = 0; fprintf(output, "return\n.end method\n");}	
		  | VOID ID L_PAREN parameter_list R_PAREN
			{									
				funcReturn = createPType(VOID_t);
				
				boolLabelNum=0;
				//set the next local var stack #
				if(strcmp($2,"main")==0){
					isMain=1;
					nextLocalVarNum=1;
				}
				else{
					isMain=0;
					nextLocalVarNum=0;
				}
				
				if(strcmp($2,"main")==0){
					fprintf(output, ".method public static main([Ljava/lang/String;)V\n");
					fprintf(output, ".limit stack 100\n.limit locals 100\n");
					fprintf(output, "new java/util/Scanner\n");
					fprintf(output, "dup\n");
					fprintf(output, "getstatic java/lang/System/in Ljava/io/InputStream;\n");
					fprintf(output, "invokespecial java/util/Scanner/<init>(Ljava/io/InputStream;)V\n");
					fprintf(output, "putstatic output/_sc Ljava/util/Scanner;\n");
				}
				else{
					fprintf(output, ".method public static %s(", $2);
					
					//params
					struct param_sem *parPtr;
					for( parPtr=$4 ; parPtr!=0 ; parPtr=(parPtr->next) ) {
						if(parPtr->pType->isError == __TRUE)continue;
						
						fprintf(output, "%c", type2char(parPtr->pType->type));
						
					}
					
					fprintf(output, ")V\n.limit stack 100\n.limit locals 100\n");
					
				}
				
				
				
				paramError = checkFuncParam( $4 );
				if( paramError == __TRUE ){
					fprintf( stdout, "########## Error at Line#%d: param(s) with several fault!! ##########\n", linenum );
					semError = __TRUE;
				}
				
				// check and insert function into symbol table
				else{
					struct SymNode *node;
					node = findFuncDeclaration( symbolTable, $2 );

					if( node != 0 ){
						if(verifyFuncDeclaration( symbolTable, $4, createPType( VOID_t ), node ) == __TRUE){	
							insertParamIntoSymTable( symbolTable, $4, scope+1, &nextLocalVarNum );				
						}
					}
					else{
						insertParamIntoSymTable( symbolTable, $4, scope+1, &nextLocalVarNum );				
						insertFuncIntoSymTable( symbolTable, $2, $4, createPType( VOID_t ), scope, __TRUE );
					}
				}
			} 
			compound_statement { funcReturn = 0; fprintf(output, "return\n.end method\n");}		  
		  ;

funct_decl : scalar_type ID L_PAREN R_PAREN SEMICOLON
			{
				insertFuncIntoSymTable( symbolTable, $2, 0, $1, scope, __FALSE );	
			}
		   | scalar_type ID L_PAREN parameter_list R_PAREN SEMICOLON
		    {
				paramError = checkFuncParam( $4 );
				if( paramError == __TRUE ){
					fprintf( stdout, "########## Error at Line#%d: param(s) with several fault!! ##########\n", linenum );
					semError = __TRUE;
				}
				else {
					insertFuncIntoSymTable( symbolTable, $2, $4, $1, scope, __FALSE );
				}
			}
		   | VOID ID L_PAREN R_PAREN SEMICOLON
			{				
				insertFuncIntoSymTable( symbolTable, $2, 0, createPType( VOID_t ), scope, __FALSE );
			}
		   | VOID ID L_PAREN parameter_list R_PAREN SEMICOLON
			{
				paramError = checkFuncParam( $4 );
				if( paramError == __TRUE ){
					fprintf( stdout, "########## Error at Line#%d: param(s) with several fault!! ##########\n", linenum );
					semError = __TRUE;	
				}
				else {
					insertFuncIntoSymTable( symbolTable, $2, $4, createPType( VOID_t ), scope, __FALSE );
				}
			}
		   ;

parameter_list : parameter_list COMMA scalar_type ID
			   {
				struct param_sem *ptr;
				ptr = createParam( createIdList( $4 ), $3 );
				param_sem_addParam( $1, ptr );
				$$ = $1;
			   }
			   | parameter_list COMMA scalar_type array_decl
			   {
				$4->pType->type= $3->type;
				param_sem_addParam( $1, $4 );
				$$ = $1;
			   }
			   | scalar_type array_decl 
			   { 
				$2->pType->type = $1->type;  
				$$ = $2;
			   }
			   | scalar_type ID { $$ = createParam( createIdList( $2 ), $1 ); }
			   ;

var_decl : scalar_type identifier_list SEMICOLON
			{
				struct varDeclParam *ptr;
				struct SymNode *newNode;
				for( ptr=$2 ; ptr!=0 ; ptr=(ptr->next) ) {						
					if( verifyRedeclaration( symbolTable, ptr->para->idlist->value, scope ) == __FALSE ) { }
					else {
						if( verifyVarInitValue( $1, ptr, symbolTable, scope ) ==  __TRUE ){	
							newNode = createVarNode( ptr->para->idlist->value, scope, ptr->para->pType );
							if(scope==0 && !ptr->isInit){
								fprintf(output, ".field public static %s %c\n", newNode->name,type2char(newNode->type->type));
							}
							else{
								if(ptr->isInit){
									newNode->varNum = ptr->assignedVarNum;
								}
								else{
									//breakpoint();//////
									if(newNode->type->type == DOUBLE_t){
										newNode->varNum = nextLocalVarNum;
										nextLocalVarNum += 2;
									}
									else{
										newNode->varNum = nextLocalVarNum++;
									}
								}
								
							}
							insertTab( symbolTable, newNode );											
						}
					}
				}
			}
			;

identifier_list : identifier_list COMMA ID
				{					
					struct param_sem *ptr;	
					struct varDeclParam *vptr;				
					ptr = createParam( createIdList( $3 ), createPType( VOID_t ) );
					vptr = createVarDeclParam( ptr, 0 );	
					addVarDeclParam( $1, vptr );
					$$ = $1; 
					//vptr->assignedVarNum = -1;
					
				}
                | identifier_list COMMA ID ASSIGN_OP logical_expression
				{
					struct param_sem *ptr;	
					struct varDeclParam *vptr;				
					ptr = createParam( createIdList( $3 ), createPType( VOID_t ) );
					vptr = createVarDeclParam( ptr, $5 );
					vptr->isArray = __TRUE;
					vptr->isInit = __TRUE;	
					addVarDeclParam( $1, vptr );	
					$$ = $1;
					if (scope == 0) {
						fprintf(output, ".field public static %s %c\n", $3, type2char(currentDeclType));
						//ignore init
					}
					else {
						if(currentDeclType > $5->pType->type){//cast r
							fprintf(output, "%c2%c\n", loadType(type2char($5->pType->type)), loadType(type2char(currentDeclType)));
						}
						fprintf(output, "%cstore %d\n", loadType(type2char(currentDeclType)), nextLocalVarNum);
						//breakpoint();//////
						if(currentDeclType == DOUBLE_t){
							vptr->assignedVarNum = nextLocalVarNum;
							nextLocalVarNum += 2;
						}
						else{
							vptr->assignedVarNum = nextLocalVarNum++;
						}
						
					}
					
					
					
				}
                | identifier_list COMMA array_decl ASSIGN_OP initial_array
				{
					struct varDeclParam *ptr;
					ptr = createVarDeclParam( $3, $5 );
					ptr->isArray = __TRUE;
					ptr->isInit = __TRUE;
					addVarDeclParam( $1, ptr );
					$$ = $1;	
				}
                | identifier_list COMMA array_decl
				{
					struct varDeclParam *ptr;
					ptr = createVarDeclParam( $3, 0 );
					ptr->isArray = __TRUE;
					addVarDeclParam( $1, ptr );
					$$ = $1;
				}
                | array_decl ASSIGN_OP initial_array
				{	
					$$ = createVarDeclParam( $1 , $3 );
					$$->isArray = __TRUE;
					$$->isInit = __TRUE;	
				}
                | array_decl 
				{ 
					$$ = createVarDeclParam( $1 , 0 ); 
					$$->isArray = __TRUE;
				}
                | ID ASSIGN_OP logical_expression
				{
					struct param_sem *ptr;					
					ptr = createParam( createIdList( $1 ), createPType( VOID_t ) );
					$$ = createVarDeclParam( ptr, $3 );		
					$$->isInit = __TRUE;
					if (scope == 0) {
						fprintf(output, ".field public static %s %c\n", $3, type2char(currentDeclType));
						//ignore init
					}
					else {
						if(currentDeclType > $3->pType->type){//cast r
							fprintf(output, "%c2%c\n", loadType(type2char($3->pType->type)), loadType(type2char(currentDeclType)));
						}
						fprintf(output, "%cstore %d\n", loadType(type2char(currentDeclType)), nextLocalVarNum);
						//breakpoint();//////
						if(currentDeclType == DOUBLE_t){
							$$->assignedVarNum = nextLocalVarNum;
							nextLocalVarNum += 2;
						}
						else{
							$$->assignedVarNum = nextLocalVarNum++;
						}
						
					}
				}
                | ID 
				{
					struct param_sem *ptr;					
					ptr = createParam( createIdList( $1 ), createPType( VOID_t ) );
					$$ = createVarDeclParam( ptr, 0 );	
					//$$->assignedVarNum = -1;	
				}
                ;
		 
initial_array : L_BRACE literal_list R_BRACE { $$ = $2; }
			  ;

literal_list : literal_list COMMA logical_expression
				{
					struct expr_sem *ptr;
					for( ptr=$1; (ptr->next)!=0; ptr=(ptr->next) );				
					ptr->next = $3;
					$$ = $1;
				}
             | logical_expression
				{
					$$ = $1;
				}
             |
             ;

const_decl 	: CONST scalar_type const_list SEMICOLON
			{
				struct SymNode *newNode;				
				struct constParam *ptr;
				for( ptr=$3; ptr!=0; ptr=(ptr->next) ){
					if( verifyRedeclaration( symbolTable, ptr->name, scope ) == __TRUE ){//no redeclare
						if( ptr->value->category != $2->type ){//type different
							if( !(($2->type==FLOAT_t || $2->type == DOUBLE_t ) && ptr->value->category==INTEGER_t) ) {
								if(!($2->type==DOUBLE_t && ptr->value->category==FLOAT_t)){	
									fprintf( stdout, "########## Error at Line#%d: const type different!! ##########\n", linenum );
									semError = __TRUE;	
								}
								else{
									newNode = createConstNode( ptr->name, scope, $2, ptr->value );
									//newNode->varNum = nextLocalVarNum++;
									insertTab( symbolTable, newNode );
								}
							}							
							else{
								newNode = createConstNode( ptr->name, scope, $2, ptr->value );
								//newNode->varNum = nextLocalVarNum++;
								insertTab( symbolTable, newNode );
							}
						}
						else{
							newNode = createConstNode( ptr->name, scope, $2, ptr->value );
							//newNode->varNum = nextLocalVarNum++;
							insertTab( symbolTable, newNode );
						}
					}
				}
			}
			;

const_list : const_list COMMA ID ASSIGN_OP literal_const
			{				
				addConstParam( $1, createConstParam( $5, $3 ) );
				$$ = $1;
			}
		   | ID ASSIGN_OP literal_const
			{
				$$ = createConstParam( $3, $1 );	
			}
		   ;

array_decl : ID dim 
			{
				$$ = createParam( createIdList( $1 ), $2 );
			}
		   ;

dim : dim ML_BRACE INT_CONST MR_BRACE
		{
			if( $3 == 0 ){
				fprintf( stdout, "########## Error at Line#%d: array size error!! ##########\n", linenum );
				semError = __TRUE;
			}
			else
				increaseArrayDim( $1, 0, $3 );			
		}
	| ML_BRACE INT_CONST MR_BRACE	
		{
			if( $2 == 0 ){
				fprintf( stdout, "########## Error at Line#%d: array size error!! ##########\n", linenum );
				semError = __TRUE;
			}			
			else{		
				$$ = createPType( VOID_t ); 			
				increaseArrayDim( $$, 0, $2 );
			}		
		}
	;
	
compound_statement : {scope++;}L_BRACE var_const_stmt_list R_BRACE
					{ 
						// print contents of current scope
						if( Opt_Symbol == 1 )
							printSymTable( symbolTable, scope );
							
						deleteScope( symbolTable, scope );	// leave this scope, delete...
						scope--; 
					}
				   ;

var_const_stmt_list : var_const_stmt_list statement	
				    | var_const_stmt_list var_decl
					| var_const_stmt_list const_decl
				    |
				    ;

statement : compound_statement
		  | simple_statement
		  | conditional_statement
		  | while_statement
		  | for_statement
		  | function_invoke_statement
		  | jump_statement
		  ;		

simple_statement : variable_reference ASSIGN_OP logical_expression SEMICOLON
					{
						// check if LHS exists
						__BOOLEAN flagLHS = verifyExistence( symbolTable, $1, scope, __TRUE );
						// id RHS is not dereferenced, check and deference
						__BOOLEAN flagRHS = __TRUE;
						if( $3->isDeref == __FALSE ) {
							flagRHS = verifyExistence( symbolTable, $3, scope, __FALSE );
						}
						// if both LHS and RHS are exists, verify their type
						if( flagLHS==__TRUE && flagRHS==__TRUE )
							verifyAssignmentTypeMatch( $1, $3 );
						//codegen
						struct SymNode *node = lookupSymbol(symbolTable, $1->varRef->id, scope, __FALSE);
						
						if($1->pType->type > $3->pType->type){//cast r
							fprintf(output, "%c2%c\n", loadType(type2char($3->pType->type)), loadType(type2char($1->pType->type)));
						}
						
						if (node->scope == 0) {
							fprintf(output, "putstatic output/%s %c\n", node->name, type2char($1->pType->type));
						}
						else {
							fprintf(output, "%cstore %d\n",loadType(type2char($1->pType->type)), node->varNum);
						}
						
						//
					}
				 | PRINT {fprintf(output, "getstatic java/lang/System/out Ljava/io/PrintStream;\n");}
						logical_expression SEMICOLON {
							verifyScalarExpr( $3, "print" );
							char c = type2char($3->pType->type);
							if (c == 'S')
								fprintf(output, "invokevirtual java/io/PrintStream/print(Ljava/lang/String;)V\n");
							else
								fprintf(output, "invokevirtual java/io/PrintStream/print(%c)V\n", c);
						}
				 | READ variable_reference SEMICOLON 
					{ 
						if( verifyExistence( symbolTable, $2, scope, __TRUE ) == __TRUE )						
							verifyScalarExpr( $2, "read" ); 
						fprintf(output, "getstatic output/_sc Ljava/util/Scanner;\n");
						switch ($2->pType->type) {
							case INTEGER_t:
								fprintf(output, "invokevirtual java/util/Scanner/nextInt()I\n");
								break;
							case BOOLEAN_t:
								fprintf(output, "invokevirtual java/util/Scanner/nextBoolean()Z\n");
								break;
							case DOUBLE_t:
								fprintf(output, "invokevirtual java/util/Scanner/nextDouble()D\n");
								break;
							case FLOAT_t:
								fprintf(output, "invokevirtual java/util/Scanner/nextFloat()F\n");
								break;
						}
						struct SymNode *node = lookupSymbol(symbolTable, $2->varRef->id, scope, __FALSE);
						if (node->scope == 0) {
							fprintf(output, "putstatic output/%s %c\n", node->name, type2char(node->type->type));
						}
						else {
							fprintf(output, "%cstore %d\n", loadType(type2char($2->pType->type)), node->varNum);
						}
						
					}
				 ;


/*
	conditional_if
	beq L_else_0
	compound_statement
L_else_0:
	
*/

/*
	conditional_if
	beq L_else_0
	compound_statement
	goto L_exit_0
L_else_0:
	compound_statement
L_exit_0:
	
*/
GenerateIFLabel:	{
						fprintf(output, "ifeq L_else_%d\n", ifLabelNum);
						$$ = ifLabelNum++;
					}
					;

conditional_statement : IF L_PAREN conditional_if  R_PAREN GenerateIFLabel compound_statement
						{
							fprintf(output, "L_else_%d:\n", $5);
						}
					  | IF L_PAREN conditional_if  R_PAREN GenerateIFLabel compound_statement
						{
							fprintf(output, "goto L_exit_%d\n", $5);
							fprintf(output, "L_else_%d:\n", $5);
						}
						ELSE compound_statement
						{
							fprintf(output, "L_exit_%d:\n", $5);
						}
					  ;
conditional_if : logical_expression { verifyBooleanExpr( $1, "if" ); };;					  

/*(while)
L_loop_start_0:
	logical_expression
	beq L_loop_exit_0
	compound_statement
	goto L_loop_start_0
L_loop_exit_0:
	
*/
/*(do-while)
Ls:
	compound_statement
	logical_expression
	bne Ls
Le: ;used for break/continue
*/
GenerateLoopLabel:	{
						fprintf(output, "L_loop_start_%d:\n", loopLabelNum);
						$$=loopLabelNum++;
						
					}
					;

while_statement : WHILE L_PAREN GenerateLoopLabel logical_expression 
					{
						verifyBooleanExpr( $4, "while" );
						fprintf(output, "ifeq L_loop_exit_%d\n", $3);
						
					} R_PAREN { inloop++;pushLoopStack($3); }
					compound_statement 
					{ 
						inloop--;
						popLoopStack();
						fprintf(output, "goto L_loop_start_%d\n", $3);
						fprintf(output, "L_loop_exit_%d:\n", $3);
					}
				|  DO GenerateLoopLabel { inloop++; pushLoopStack($2);} compound_statement WHILE L_PAREN logical_expression R_PAREN SEMICOLON  
					{ 
						 verifyBooleanExpr( $7, "while" );
						 inloop--; 
						 popLoopStack();
						fprintf(output, "ifne L_loop_start_%d\n", $2);
						fprintf(output, "L_loop_exit_%d:\n", $2);
					}
				;


/*
	initial_expression
Lsf:
	control_expression
	beq Le
	goto Lb
Ls:
	increment_expression
	goto Lsf
Lb:
	compound_statement
	goto Ls
Le:
	(change the label names due to continue)
*/
GenerateForLabel:	{
						fprintf(output, "L_loop_startf_%d:\n", loopLabelNum);
						$$=loopLabelNum++;
						
					}
					;

for_statement : FOR L_PAREN initial_expression SEMICOLON GenerateForLabel control_expression SEMICOLON 
				{
					fprintf(output, "ifeq L_loop_exit_%d\n", $5);
					fprintf(output, "goto L_loop_body_%d\n", $5);
					fprintf(output, "L_loop_start_%d:\n", $5);
					
				} increment_expression R_PAREN 
				{
					inloop++;
					pushLoopStack($5);
					fprintf(output, "goto L_loop_startf_%d\n", $5);
					fprintf(output, "L_loop_body_%d:\n", $5);
				}
					compound_statement 
				{
					inloop--;
					popLoopStack();
					fprintf(output, "goto L_loop_start_%d\n", $5);
					fprintf(output, "L_loop_exit_%d:\n", $5);
				}
			  ;

initial_expression : initial_expression COMMA statement_for		
				   | initial_expression COMMA logical_expression
				   | logical_expression	
				   | statement_for
				   |
				   ;

control_expression : control_expression COMMA statement_for
				   {
						fprintf( stdout, "########## Error at Line#%d: control_expression is not boolean type ##########\n", linenum );
						semError = __TRUE;	
				   }
				   | control_expression COMMA logical_expression
				   {
						if( $3->pType->type != BOOLEAN_t ){
							fprintf( stdout, "########## Error at Line#%d: control_expression is not boolean type ##########\n", linenum );
							semError = __TRUE;	
						}
				   }
				   | logical_expression 
					{ 
						if( $1->pType->type != BOOLEAN_t ){
							fprintf( stdout, "########## Error at Line#%d: control_expression is not boolean type ##########\n", linenum );
							semError = __TRUE;	
						}
					}
				   | statement_for
				   {
						fprintf( stdout, "########## Error at Line#%d: control_expression is not boolean type ##########\n", linenum );
						semError = __TRUE;	
				   }
				   | {fprintf(output, "iconst_1\n");}
				   ;

increment_expression : increment_expression COMMA statement_for
					 | increment_expression COMMA logical_expression
					 | logical_expression
					 | statement_for
					 |
					 ;

statement_for 	: variable_reference ASSIGN_OP logical_expression
					{
						// check if LHS exists
						__BOOLEAN flagLHS = verifyExistence( symbolTable, $1, scope, __TRUE );
						// id RHS is not dereferenced, check and deference
						__BOOLEAN flagRHS = __TRUE;
						if( $3->isDeref == __FALSE ) {
							flagRHS = verifyExistence( symbolTable, $3, scope, __FALSE );
						}
						// if both LHS and RHS are exists, verify their type
						if( flagLHS==__TRUE && flagRHS==__TRUE )
							verifyAssignmentTypeMatch( $1, $3 );
						//codegen
						struct SymNode *node = lookupSymbol(symbolTable, $1->varRef->id, scope, __FALSE);
						
						if($1->pType->type > $3->pType->type){//cast r
							fprintf(output, "%c2%c\n", loadType(type2char($3->pType->type)), loadType(type2char($1->pType->type)));
						}
						
						if (node->scope == 0) {
							fprintf(output, "putstatic output/%s %c\n", node->name, type2char($1->pType->type));
						}
						else {
							fprintf(output, "%cstore %d\n",loadType(type2char($1->pType->type)), node->varNum);
						}
						
						//
					}
					;
					 

function_invoke_statement : ID L_PAREN {
									struct SymNode *node = findFuncDeclaration(symbolTable, $1);
									currentFuncCallParam = node->attribute->formalParam->params;
									
								} logical_expression_list R_PAREN SEMICOLON
							{
								verifyFuncInvoke( $1, $4, symbolTable, scope );
								
								//codegen
								fprintf(output, "invokestatic output/%s(", $1);
								
								struct SymNode *node = findFuncDeclaration(symbolTable, $1);
								if(node!=0){
									struct PTypeList *currentParam = node->attribute->formalParam->params;
									for(;currentParam!=0;currentParam=currentParam->next){
										fprintf(output, "%c", type2char(currentParam->value->type));
										
									}
									
								}
								fprintf(output, ")%c\n", type2char(node->type->type));
								
								//
							}
						  | ID L_PAREN R_PAREN SEMICOLON
							{
								verifyFuncInvoke( $1, 0, symbolTable, scope );
								struct SymNode *node = findFuncDeclaration(symbolTable, $1);
								fprintf(output, "invokestatic output/%s()%c\n", $1, type2char(node->type->type));
							}
						  ;

jump_statement : CONTINUE SEMICOLON
				{
					if( inloop <= 0){
						fprintf( stdout, "########## Error at Line#%d: continue can't appear outside of loop ##########\n", linenum ); semError = __TRUE;
					}
					else
						fprintf(output, "goto L_loop_start_%d\n", loopStackTop->loopNum);
				}
			   | BREAK SEMICOLON 
				{
					if( inloop <= 0){
						fprintf( stdout, "########## Error at Line#%d: break can't appear outside of loop ##########\n", linenum ); semError = __TRUE;
					}
					else
						fprintf(output, "goto L_loop_exit_%d\n", loopStackTop->loopNum);
				}
			   | RETURN logical_expression SEMICOLON
				{
					verifyReturnStatement( $2, funcReturn );
					
					if(isMain){
						fprintf(output, "return\n");
					}
					else{
						if(funcReturn->type > $2->pType->type){//cast r
							fprintf(output, "%c2%c\n", loadType(type2char($2->pType->type)), loadType(type2char(funcReturn->type)));
						}
						fprintf(output, "%creturn\n", loadType(type2char(funcReturn->type)));
					}
					
				}
			   ;

variable_reference : ID
					{
						$$ = createExprSem( $1 );
					}
				   | variable_reference dimension
					{	
						increaseDim( $1, $2 );
						$$ = $1;
					}
				   ;

dimension : ML_BRACE arithmetic_expression MR_BRACE
			{
				$$ = verifyArrayIndex( $2 );
			}
		  ;
		  
logical_expression : logical_expression OR_OP logical_term
					{
						verifyAndOrOp( $1, OR_t, $3 );
						$$ = $1;
						//codegen
						fprintf(output, "ior\n");
						//
					}
				   | logical_term { $$ = $1; }
				   ;

logical_term : logical_term AND_OP logical_factor
				{
					verifyAndOrOp( $1, AND_t, $3 );
					$$ = $1;
					//codegen
					fprintf(output, "iand\n");
					//
				}
			 | logical_factor { $$ = $1; }
			 ;

logical_factor : NOT_OP logical_factor
				{
					verifyUnaryNot( $2 );
					$$ = $2;
					//codegen
					fprintf(output, "iconst_1\n");
					fprintf(output, "ixor\n");
					//
				}
			   | relation_expression { $$ = $1; }
			   ;

relation_expression : arithmetic_expression relation_operator arithmetic_expression
					{
						SEMTYPE ltype = $1->pType->type, rtype = $3->pType->type;
						
						verifyRelOp( $1, $2, $3 );
						$$ = $1;
						
						//codegen
						if(ltype == BOOLEAN_t){
							//bool (only eq)
							fprintf(output, "ixor\n");
							fprintf(output, "iconst_1\n");
							fprintf(output, "ixor\n");
						}
						else{
							ifdCast(ltype, rtype, nextLocalVarNum);
							
							SEMTYPE larger=ltype;
							if(rtype>ltype) larger=rtype;//find larger type of l and r
							
							char c=loadType(type2char(larger));
							if(c == 'i'){
								fprintf(output, "isub\n");
							}
							else{
								fprintf(output, "%ccmpl\n", c);
							}
							
							switch($2){
								case LT_t:
									fprintf(output, "iflt");
									break;
								case LE_t:
									fprintf(output, "ifle");
									break;
								case EQ_t:
									fprintf(output, "ifeq");
									break;
								case GE_t:
									fprintf(output, "ifge");
									break;
								case GT_t:
									fprintf(output, "ifgt");
									break;
								case NE_t:
									fprintf(output, "ifne");
									break;
							}
							/*
								iflt L1
								iconst_0 ; false = 0
								goto L2
								L1:
								iconst_1 ; true = 1
								L2:
							*/
							fprintf(output, " L%d\n", boolLabelNum);
							
							fprintf(output, "iconst_0\n");
							fprintf(output, "goto L%d\n", boolLabelNum + 1);
							fprintf(output, "L%d:\n", boolLabelNum);
							fprintf(output, "iconst_1\n");
							fprintf(output, "L%d:\n", boolLabelNum + 1);
							
							boolLabelNum += 2;
							
						}
						//
					}
					| arithmetic_expression { $$ = $1; }
					;

relation_operator : LT_OP { $$ = LT_t; }
				  | LE_OP { $$ = LE_t; }
				  | EQ_OP { $$ = EQ_t; }
				  | GE_OP { $$ = GE_t; }
				  | GT_OP { $$ = GT_t; }
				  | NE_OP { $$ = NE_t; }
				  ;

arithmetic_expression : arithmetic_expression add_op term
			{
				SEMTYPE ltype = $1->pType->type, rtype = $3->pType->type;
				
				verifyArithmeticOp( $1, $2, $3 );
				$$ = $1;
				
				//codegen
				ifdCast(ltype, rtype, nextLocalVarNum);
				if($2==ADD_t){
					fprintf(output, "%cadd\n", loadType(type2char($1->pType->type)));
				}
				else if($2==SUB_t){
					fprintf(output, "%csub\n", loadType(type2char($1->pType->type)));
				}
				//
			}
                   | relation_expression { $$ = $1; }
		   | term { $$ = $1; }
		   ;

add_op	: ADD_OP { $$ = ADD_t; }
		| SUB_OP { $$ = SUB_t; }
		;
		   
term : term mul_op factor
		{
			SEMTYPE ltype = $1->pType->type, rtype = $3->pType->type;
			
			if( $2 == MOD_t ) {
				verifyModOp( $1, $3 );
			}
			else {
				verifyArithmeticOp( $1, $2, $3 );
			}
			$$ = $1;
			
			//codegen
			ifdCast(ltype, rtype, nextLocalVarNum);
			if($2==MOD_t){
				fprintf(output, "irem\n");
			}
			else if($2==MUL_t){
				fprintf(output, "%cmul\n", loadType(type2char($1->pType->type)));
			}
			else if($2==DIV_t){
				fprintf(output, "%cdiv\n", loadType(type2char($1->pType->type)));
			}
			//
		}
     | factor { $$ = $1; }
	 ;

mul_op 	: MUL_OP { $$ = MUL_t; }
		| DIV_OP { $$ = DIV_t; }
		| MOD_OP { $$ = MOD_t; }
		;
		
factor : variable_reference
		{
			verifyExistence( symbolTable, $1, scope, __FALSE );
			$$ = $1;
			$$->beginningOp = NONE_t;
			//code gen
			struct SymNode *node = lookupSymbol(symbolTable, $1->varRef->id, scope, __FALSE);
			if (node->category == CONSTANT_t) {
				//const
				
				switch(node->type->type){
				 case INTEGER_t:
					 fprintf(output, "ldc %d\n", node->attribute->constVal->value.integerVal);
					 break;
				 case FLOAT_t:
					 fprintf(output, "ldc %f\n", node->attribute->constVal->value.floatVal);
					 break;
				 case DOUBLE_t:
					 fprintf(output, "ldc2_w %lf\n", node->attribute->constVal->value.doubleVal);
					 break;
				 case BOOLEAN_t:
					 fprintf(output, "ldc %d\n", node->attribute->constVal->value.booleanVal);
					 break;
				 case STRING_t:
					 fprintf(output, "ldc \"%s\"\n", node->attribute->constVal->value.stringVal);
					 break;
				}
			}
			else{
				if(node->scope == 0){
					//global
					fprintf(output, "getstatic output/%s %c\n", node->name, type2char(node->type->type));
				}
				else{
					//local
					
					fprintf(output, "%cload %d\n",loadType(type2char(node->type->type)), node->varNum);
				}
			}
			//
		}
	   | SUB_OP variable_reference
		{
			if( verifyExistence( symbolTable, $2, scope, __FALSE ) == __TRUE )
			verifyUnaryMinus( $2 );
			$$ = $2;
			$$->beginningOp = SUB_t;
			//code gen
			struct SymNode *node = lookupSymbol(symbolTable, $2->varRef->id, scope, __FALSE);
			if (node->category == CONSTANT_t) {
				//const
				
				switch(node->type->type){
				 case INTEGER_t:
					 fprintf(output, "ldc %d\n", node->attribute->constVal->value.integerVal);
					 break;
				 case FLOAT_t:
					 fprintf(output, "ldc %f\n", node->attribute->constVal->value.floatVal);
					 break;
				 case DOUBLE_t:
					 fprintf(output, "ldc2_w %lf\n", node->attribute->constVal->value.doubleVal);
					 break;
				 case BOOLEAN_t:
					 fprintf(output, "ldc %d\n", node->attribute->constVal->value.booleanVal);
					 break;
				 case STRING_t:
					 fprintf(output, "ldc \"%s\"\n", node->attribute->constVal->value.stringVal);
					 break;
				}
			}
			else{
				if(node->scope == 0){
					//global
					fprintf(output, "getstatic output/%s %c\n", node->name, type2char(node->type->type));
				}
				else{
					//local
					
					fprintf(output, "%cload %d\n",loadType(type2char(node->type->type)), node->varNum);
				}
			}
			fprintf(output, "%cneg\n", loadType(type2char(node->type->type)));
			//
		}		
	   | L_PAREN logical_expression R_PAREN
		{
			$2->beginningOp = NONE_t;
			$$ = $2; 
		}
	   | SUB_OP L_PAREN logical_expression R_PAREN
		{
			verifyUnaryMinus( $3 );
			$$ = $3;
			$$->beginningOp = SUB_t;
			//codegen
			fprintf(output, "%cneg\n", loadType(type2char($3->pType->type)));
			//
		}
	   | ID L_PAREN {
					struct SymNode *node = findFuncDeclaration(symbolTable, $1);
					currentFuncCallParam = node->attribute->formalParam->params;
					
				} logical_expression_list R_PAREN
		{
			$$ = verifyFuncInvoke( $1, $4, symbolTable, scope );
			$$->beginningOp = NONE_t;
			//codegen
			fprintf(output, "invokestatic output/%s(", $1);
			
			struct SymNode *node = findFuncDeclaration(symbolTable, $1);
			if(node!=0){
				struct PTypeList *currentParam = node->attribute->formalParam->params;
				for(;currentParam!=0;currentParam=currentParam->next){
					fprintf(output, "%c", type2char(currentParam->value->type));
					
				}
				
			}
			fprintf(output, ")%c\n", type2char(node->type->type));
			
			//
			
		}
	   | SUB_OP ID L_PAREN {
					struct SymNode *node = findFuncDeclaration(symbolTable, $2);
					currentFuncCallParam = node->attribute->formalParam->params;
					
				} logical_expression_list R_PAREN
	    {
			$$ = verifyFuncInvoke( $2, $5, symbolTable, scope );
			$$->beginningOp = SUB_t;
			//codegen
			fprintf(output, "invokestatic output/%s(", $2);
			
			struct SymNode *node = findFuncDeclaration(symbolTable, $2);
			if(node!=0){
				struct PTypeList *currentParam = node->attribute->formalParam->params;
				for(;currentParam!=0;currentParam=currentParam->next){
					fprintf(output, "%c", type2char(currentParam->value->type));
					
				}
				
			}
			fprintf(output, ")%c\n", type2char(node->type->type));
			fprintf(output, "%cneg\n", loadType(type2char(node->type->type)));
			//
		}
	   | ID L_PAREN R_PAREN
		{
			$$ = verifyFuncInvoke( $1, 0, symbolTable, scope );
			$$->beginningOp = NONE_t;
			struct SymNode *node = findFuncDeclaration(symbolTable, $1);
			fprintf(output, "invokestatic output/%s()%c\n", $1, type2char(node->type->type));
		}
	   | SUB_OP ID L_PAREN R_PAREN
		{
			$$ = verifyFuncInvoke( $2, 0, symbolTable, scope );
			$$->beginningOp = SUB_OP;
			
			struct SymNode *node = findFuncDeclaration(symbolTable, $2);
			fprintf(output, "invokestatic output/%s()%c\n", $2, type2char(node->type->type));
			fprintf(output, "%cneg\n", loadType(type2char(node->type->type)));
		}
	   | literal_const
	    {
			  $$ = (struct expr_sem *)malloc(sizeof(struct expr_sem));
			  $$->isDeref = __TRUE;
			  $$->varRef = 0;
			  $$->pType = createPType( $1->category );
			  $$->next = 0;
			  if( $1->hasMinus == __TRUE ) {
			  	$$->beginningOp = SUB_t;
			  }
			  else {
				$$->beginningOp = NONE_t;
			  }
			  //codegen
				
				switch($1->category){
				 case INTEGER_t:
					 fprintf(output, "ldc %d\n", $1->value.integerVal);
					 break;
				 case FLOAT_t:
					 fprintf(output, "ldc %f\n", $1->value.floatVal);
					 break;
				 case DOUBLE_t:
					 fprintf(output, "ldc2_w %lf\n", $1->value.doubleVal);
					 break;
				 case BOOLEAN_t:
					 fprintf(output, "ldc %d\n", $1->value.booleanVal);
					 break;
				 case STRING_t:
					 fprintf(output, "ldc \"%s\"\n", $1->value.stringVal);
					 break;
				}
			
			  //
		}
	   ;

logical_expression_list : logical_expression_list COMMA logical_expression
						{
			  				struct expr_sem *exprPtr;
			  				for( exprPtr=$1 ; (exprPtr->next)!=0 ; exprPtr=(exprPtr->next) );
			  				exprPtr->next = $3;
			  				$$ = $1;
							//codegen
							if(currentFuncCallParam != 0){
								if(currentFuncCallParam->value->type > $3->pType->type){//cast r
									fprintf(output, "%c2%c\n", loadType(type2char($3->pType->type)), loadType(type2char(currentFuncCallParam->value->type)));
								}
								currentFuncCallParam = currentFuncCallParam->next;
							}
							//
						}
						| logical_expression {
							$$ = $1;
							//codegen
							if(currentFuncCallParam != 0){
								if(currentFuncCallParam->value->type > $1->pType->type){//cast r
									fprintf(output, "%c2%c\n", loadType(type2char($1->pType->type)), loadType(type2char(currentFuncCallParam->value->type)));
								}
								currentFuncCallParam = currentFuncCallParam->next;
							}
							
							//
						}
						;

		  


scalar_type : INT { $$ = createPType( INTEGER_t ); currentDeclType=INTEGER_t;}
			| DOUBLE { $$ = createPType( DOUBLE_t ); currentDeclType=DOUBLE_t;}
			| STRING { $$ = createPType( STRING_t ); currentDeclType=STRING_t;}
			| BOOL { $$ = createPType( BOOLEAN_t ); currentDeclType=BOOLEAN_t;}
			| FLOAT { $$ = createPType( FLOAT_t ); currentDeclType=FLOAT_t;}
			;
 
literal_const : INT_CONST
				{
					int tmp = $1;
					$$ = createConstAttr( INTEGER_t, &tmp );
				}
			  | SUB_OP INT_CONST
				{
					int tmp = -$2;
					$$ = createConstAttr( INTEGER_t, &tmp );
				}
			  | FLOAT_CONST
				{
					float tmp = $1;
					$$ = createConstAttr( FLOAT_t, &tmp );
				}
			  | SUB_OP FLOAT_CONST
			    {
					float tmp = -$2;
					$$ = createConstAttr( FLOAT_t, &tmp );
				}
			  | SCIENTIFIC
				{
					double tmp = $1;
					$$ = createConstAttr( DOUBLE_t, &tmp );
				}
			  | SUB_OP SCIENTIFIC
				{
					double tmp = -$2;
					$$ = createConstAttr( DOUBLE_t, &tmp );
				}
			  | STR_CONST
				{
					$$ = createConstAttr( STRING_t, $1 );
				}
			  | TRUE
				{
					SEMTYPE tmp = __TRUE;
					$$ = createConstAttr( BOOLEAN_t, &tmp );
				}
			  | FALSE
				{
					SEMTYPE tmp = __FALSE;
					$$ = createConstAttr( BOOLEAN_t, &tmp );
				}
			  ;
%%

int yyerror( char *msg )
{
    fprintf( stderr, "\n|--------------------------------------------------------------------------\n" );
	fprintf( stderr, "| Error found in Line #%d: %s\n", linenum, buf );
	fprintf( stderr, "|\n" );
	fprintf( stderr, "| Unmatched token: %s\n", yytext );
	fprintf( stderr, "|--------------------------------------------------------------------------\n" );
	exit(-1);
}


