module IMP-SYNTAX

syntax AExp ::= Int
				| Id
				| String
				| Float
				| "++" Id  		
				| Id "++"     
				| Id "--"
				| "--" Id
				| "-" AExp
				| "("AExp")"			[bracket]
				| Id "[" AExp "]"	
				| "*" Id
				| "&" Id
				| "scanf" "(" ")"
				| "strlen" "(" AExp ")"	
				> left:
				AExp "*" AExp			[left, strict]
				| AExp "/" AExp			[left, strict, division]
				| AExp "%" AExp			[left, strict]
				> left:
				AExp "+" AExp			[left, strict]
				| AExp "-" AExp			[left, strict]
				
				
				
syntax BExp ::= Bool
				| "!" BExp				[strict]
				>left:
			    AExp ">" AExp			[strict]
				| AExp ">=" AExp		[strict]
				| AExp "<" AExp			[strict]
				| AExp "<=" AExp		[strict]
				>left:
				AExp "==" AExp			[strict]
				| AExp "!=" AExp		[strict]
				>left:
			    BExp "&&" BExp 			[strict]
				>left:
			    BExp "||"	BExp		[strict]
				| "("BExp")"			[bracket]					
				
				

syntax Stmt ::= Blocks
				| AExp ";"																		[strict]
				| "int" "*" Id ";"
				| "float" "*" Id ";"
				| "int" VarDecls ";"
				| "string" VarDecls ";"
				| "float" VarDecls ";"
				| Id "=" AExp ";"						            							[strict(2)]
				| Id "+=" AExp ";"																[strict(2)]
				| Id "-=" AExp ";"																[strict(2)]
				| Id "/=" AExp ";"																[strict(2)]
				| Id "*=" AExp ";"																[strict(2)]
				| Id "%=" AExp ";"																[strict(2)]
				| Id "[" AExp "]" "=" AExp ";"	
				| Id "("CallParams")" 						[strict(2)]
				| "if" "("BExp")" Blocks "else" Blocks	    [strict(1), avoid]
				| "if" "(" BExp ")" Stmt
				| "while" "(" BExp ")" Blocks
				| "do" Blocks "while" "("BExp")" ";"
				| "for" "(" Stmt BExp ";" Stmt ")" Blocks
				| "("BExp")" "?" Blocks ":" Blocks ";"		[strict(1)]	
				| "print" "(" Specifiers "," AExp ")" ";"  
				| "printf" "(" CallParams ")" ";"				
				| "return" ";"
				| "return" AExp ";"							[strict]
				| "thread" Stmt
				| "sync" AExp ";"       
				> "spawn" Stmt
				> Stmt Stmt									[right]
			

syntax Blocks ::= "{" "}"
				  |"{" Stmt "}"
				  
syntax Ids ::= List{Id, ","}
syntax Exps ::= List{AExp, ","}          					[strict]
syntax Pgm ::= List{Decl, ";"}
syntax Decl ::= "int" VarDecls | "float" VarDecls | "string" VarDecls | FunDecl
syntax VarDecl ::= 	Id
					| Id "[" AExp "]"						[strict(2) , avoid]
					| Id "=" AExp    						[strict(2)]
					
syntax VarDecls ::= List{VarDecl, ","}
syntax CallParams ::= List{AExp, ","}
syntax FunDecl ::= "function" Id "("ParamDeclList")" Blocks
syntax Specifiers ::= "%d" | "%s" | "%f"

syntax ParamDecl ::= "int" Id 
					| "string" Id 
					| "int" Id "[" AExp "]"					[strict(2)]
					| "string" Id "[" AExp "]"				[strict(2)]
					
syntax ParamDeclList ::= List{ParamDecl, ","}




endmodule

module IMP

imports IMP-SYNTAX
imports FLOAT
imports STRING


syntax Val ::= Int | Float | String | Bool | Id
syntax Vals ::= List{Val, ","}
syntax Result ::= String | Int | Bool | Float
syntax ListResult ::= List{Result, ","}
syntax KResult ::= Result | ListResult
syntax AExp ::= Val
syntax CallParams ::= Vals

syntax KItem ::= "execute"
syntax Id ::= "main"        	[token]


configuration 	<T>
						<k>$PGM:Pgm ~> execute </k>
							<env> .Map </env>
							<store> .Map </store>
						<in stream="stdin"> .List </in>
						<out stream="stdout"> .List </out>
						<fstack> .List </fstack>
						<next> 0 </next>
						</T>
				
/* RULE FOR NEGATIVE NUMBERS */

rule - I => 0 -Int I	

/* RULE FOR STRING CONCATENARTION AND LENGTH*/

rule S:String + Q:String => S +String Q	
rule strlen(S:String) => lengthString(S)		

/* RULES FOR VARIABLES DECLARATION */

rule <k> (float X:Id ; => .) ...</k>
     <env> M:Map => M[X <- !L:Int] </env>
     <store> Sigma:Map (.Map => (!L |-> 0.0)) </store>
	   
rule <k> (int X:Id ; => .) ...</k>
     <env> M:Map => M[X <- !L:Int] </env>
     <store> Sigma:Map (.Map => (!L |-> 0)) </store>
	 
rule <k> (string X:Id ; => .) ...</k>
     <env> M:Map => M[X <- !L:Int] </env>
     <store> Sigma:Map (.Map => (!L |-> "start")) </store>
	 
/*RULES FOR MULTIPLE DECLARATION*/
rule <k> int (X, Xs => Xs) ; ...</k>
	 <env> M:Map => M[X <- !N:Int] </env>
	 <store> Sigma:Map (.Map => (!N |-> 0)) </store>
	 

/*RULE FOR GLOBAL DECLARATION*/
rule int .Ids; => .

/* RULES FOR INTEGER VALUES */

rule I1:Int + I2:Int => I1 +Int I2
rule I1:Int - I2:Int => I1 -Int I2
rule I1:Int * I2:Int => I1 *Int I2
rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0
rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=Int 0

/* RULES FOR FLOAT VALUES */

rule F1:Float + F2:Float => F1 +Float F2
rule F1:Float - F2:Float => F1 -Float F2 
rule F1:Float * F2:Float => F1 *Float F2 
rule F1:Float / F2:Float => F1 /Float F2 when F2 =/=Float 0.0

/* RULES FOR BOOLEAN EXPRESSION */

rule B1:Int >  B2:Int => B1 >Int B2
rule B1:Int >= B2:Int => B1 >=Int B2
rule B1:Int <  B2:Int => B1 <Int B2
rule B1:Int <= B2:Int => B1 <=Int B2
rule B1:Int == B2:Int => B1 ==Int B2
rule B1:Int != B2:Int => B1 =/=Int B2

/* RULES FOR STRING COMPARATION */

rule S1:String > S2:String => S1 >String S2
rule S1:String >= S2:String => S1 >=String S2
rule S1:String < S2:String => S1 <String S2
rule S1:String <= S2:String => S1 <=String S2
rule S1:String == S2:String => S1 ==String S2
rule S1:String != S2:String => S1 =/=String S2

/* RULES FOR "&&", "||", "!" */

rule ! B:Bool => notBool B
rule false && _ => false
rule true && B:Bool => B
rule true || _ => true
rule false || B:Bool => B
rule B1:Bool == B2:Bool => (B1 && B2) || (notBool(B1) && notBool(B2))
rule B1:Bool != B2:Bool => (B1 || B2) && (notBool(B1) || notBool(B2))

/* RULES FOR ASSIGNMENT */
 

rule <k> (X:Id [I:Int] = V:Int ; => .) ...</k>
			<env>... X |-> L:Int </env>
			<store>... L +Int I |-> (_ => V) </store>
			
	rule <k> (X:Id [I:Int] = V:String ; => .) ...</k>
			<env>... X |-> L:Int </env>
			<store>... L +Int I |-> (_ => V) </store>
	 
rule <k> (X:Id = V:Int ; => .) ...</k>
	 <env>... X |-> L:Int </env>
	 <store>... L |-> (_ => V) </store>

rule <k> (X:Id = V:Float ; => .) ...</k>
   	 <env>... X |-> L:Int </env>
	 <store>... L |-> (_ => V) </store>

rule <k> (X:Id = V:String ; => .) ...</k>
   	 <env>... X |-> L:Int </env>
	 <store>... L |-> (_ => V) </store>
	 
	 
/* RULES FOR VARIABLES DECLARATION + ASSIGNMENT */

rule <k> (int X:Id = V:Int ; => . ) ...</k>
	 <env> M:Map => M[X <- !N:Int] </env>
	 <store> Sigma:Map (.Map => (!N |-> V)) </store>
	 
rule <k> (float X:Id = V:Float ; => . ) ...</k>
	 <env> M:Map => M[X <- !N:Int] </env>
	 <store> Sigma:Map (.Map => (!N |-> V)) </store>
	 
rule <k> (string X:Id = V:String ; => . ) ...</k>
	 <env> M:Map => M[X <- !N:Int] </env>
	 <store> Sigma:Map (.Map => (!N |-> V)) </store>	
	 
	 
/* RULES FOR LOOKUP */

rule <k> (X:Id => V) ...</k>
	 <env>... X |-> L:Int ...</env>
	 <store>... L |-> V:Result ...</store>
			
//rules for pointers
			
rule <k> (& X:Id => L)...</k>
	 <env>... X |-> L:Int ...</env>

	 
/* RULES FOR ASSIGNMENT OPERATORS */
	
/* INTERGER */
	
rule <k> (X:Id += V:Int ; => .) ...</k>
	 <env>... X |-> L:Int </env>
	 <store>... L |-> (?_ => ?_ +Int V) </store>
	 
rule <k> (X:Id -= V:Int ; => .) ...</k>
	 <env>... X |-> L:Int </env>
	 <store>... L |-> (?_ => ?_ -Int V) </store>

rule <k> (X:Id *= V:Int ; => .) ...</k>
	 <env>... X |-> L:Int </env>
	 <store>... L |-> (?_ => ?_ *Int V) </store>

rule <k> (X:Id /= V:Int ; => .) ...</k>
	 <env>... X |-> L:Int </env>
	 <store>... L |-> (?_ => ?_ /Int V) </store>
	 
/* RULE FOR STRING CONCATENATION USING "=+" OPERATOR */
	 	 
rule <k> (X:Id += V:String ; => .) ...</k>
	 <env>... X |-> L:Int </env>
	 <store>... L |-> (?_ => ?_ +String V) </store>
 
	 
/* INCREMENT OPERATORS */

rule <k> X:Id ++  => V ...</k>
	 <env>... X|-> N ...</env>
	 <store>... N |-> (V => V +Int 1)  ...</store>
	 
rule <k> ++ X:Id  => V +Int 1 ...</k>
	 <env>... X|-> N ...</env>
	 <store>... N |-> (V => V +Int 1) ...</store>
	 
/* DECREMENT OPERATORS */
	 
rule <k> X:Id --  => V ...</k>
	 <env>... X|-> N ...</env>
	 <store>... N |-> (V => V -Int 1)  ...</store>
	 
rule <k> -- X:Id  => V -Int 1 ...</k>
	 <env>... X|-> N ...</env>
	 <store>... N |-> (V => V -Int 1)  ...</store>
	 
/* RULE FOR STATEMENT SEQUENCES */
	 
rule S1:Stmt S2:Stmt => S1 ~> S2

rule F:Float ; => .
rule I:Int ; => .
rule S:String ; => .
rule B:Bool ; => .

/* RULES FOR BLOCKS */

syntax K ::= env(Map)
rule <k>{S} => S ~> env(Rho) ...</k>
	 <env> Rho </env>
rule <k> env(Rho) => . ...</k> <env> _ => Rho </env>

/* RULE FOR EMPTY BLOCKS */
rule {} => . 
	 
/*RULES FOR "if...else" STATEMENT*/
rule if(true)  B:Blocks else _ => B
rule if(false)  _ else B:Blocks => B 


/* RULES FOR "while", "do...while", "for" STATEMENTS */
rule while (C) { S }=> if (C)  { S while (C)  { S } } else {}
rule do { S:Stmt } while (C:BExp) ; => S:Stmt while (C:BExp) { S:Stmt }	
rule for ( Start:Stmt C:BExp ; Step:Stmt ) { S:Stmt } => { Start while (C) { S Step } }

/*RULES FOR "scanf" STATEMENT*/
rule <k> scanf() => I ...</k>
			<in> (ListItem(I:Int) => .List) ...</in>
	 
/*RULES FOR WHAT CAN BE PRINTED*/
syntax Printable ::= Int | String | Float
syntax AExp ::= Printable

	 
/*RULES FOR "printf" STATEMENT*/


rule <k> (print(%d, I:Int) ; => .) ...</k>
     <out>... (.List => ListItem(I)) </out>

rule <k> (print(%s, I:String) ; => .) ...</k>
     <out>... (.List => ListItem(I)) </out>
	 
rule <k> (print(%f, I:Float) ; => .) ...</k>
     <out>... (.List => ListItem(I)) </out>  	 

		
rule <k> printf(V:Printable, Es:CallParams => Es); ...</k> 
		<out>... .List => ListItem(V) </out>
		
rule <k> printf(V:Id , Es:CallParams => Es); ...</k> 
		<out>... .List => ListItem(I) </out>
		<env> ... V |-> L ... </env>
		<store> ... L |-> I ... </store>
		
rule printf(.CallParams); => .
	 


/* RULES FOR DECISIONAL STATEMENTS */
rule (B:BExp) ? S1:Blocks : S2:Blocks ; => if(B) S1 else S2	  



/*-----------FUNCTIONS----------*/

/* RULES FOR FUNCTIONS DECLARATION */
 
syntax Lambda ::= "lambda" "(" ParamDeclList  "," Blocks ")" 

rule <k> ( function X:Id ( P:ParamDeclList ) B:Blocks => . ) ...</k>
     <env> Rho => Rho[X <- !L:Int]  </env>
     <store> Sigma => Sigma[!L <- lambda(P, B)] </store>
	  
	  
/*main() => the entry point of the execution*/

rule .Pgm ~> execute => main(.CallParams) 

/*RULES FOR SEQUENCES OF DECLARATIONS*/

rule D:Decl ; Ds:Pgm => D ~> Ds

/*RULES FOR FUNCTION CALL*/

syntax KItem ::= "saveEnv"
syntax KItem ::= "mkDecl" "(" ParamDeclList  "," Vals ")" 

rule <k> X:Id ( P:Vals ) => saveEnv ~> mkDecl(Ds, P) ~> S ...</k>
     <env>... X |-> L:Int ...</env>
     <store>... L |-> lambda(Ds:ParamDeclList , { S } ) ...</store>

/*RULES FOR SAVING THE ENVIRONMENT*/

rule <k> (saveEnv => .) ...</k>
     <env> Rho </env>
     <fstack> (.List => ListItem(Rho)) ...</fstack>

/*RULES FOR DECLARATIONS*/

rule mkDecl(.ParamDeclList, .Vals) => .

rule <k> mkDecl ( (int X:Id, Xs:ParamDeclList ), (V:Int, Vs:Vals) ) =>  mkDecl(Xs, Vs) ...</k>  
     <env> Rho => Rho[X <- !L:Int] </env>
     <store> Sigma => Sigma[!L <- V] </store>

/* RULES FOR "return"(value) STATEMENT */

rule <k> return V:Val ; => V ...</k>
     <env> _ => Rho </env>
     <fstack> (ListItem(Rho) => .List) ...</fstack>
  
/*RULES FOR "return;" STATEMENT */

rule <k> return ; => . ...</k>
     <env> _ => Rho </env>
     <fstack> (ListItem(Rho) => .List) ...</fstack>

/*RULES FOR ARRAY */



endmodule