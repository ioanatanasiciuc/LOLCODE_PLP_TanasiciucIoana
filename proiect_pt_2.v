Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.

(* OPERATII ARITMETICE *)   

(* TIP BOOL *)



Inductive TROOF :=
| ttroof : bool -> TROOF.

Coercion ttroof : bool >-> TROOF.

Notation " 'WIN' " := (ttroof true) (at level 50).
Notation " 'FAIL' " := (ttroof false) (at level 50).

Check WIN.
Check FAIL.
Check true.

(* TIP STRING *)

Require Import String.
Open Scope string_scope.


Inductive YARN :=
| yyarn : string -> YARN.

Coercion yyarn : string >-> YARN.

Check YARN.
Check string.
Check yyarn "Hello".
Check "Hello".


(* TIP INT *)

Inductive NUMBR :=
| nnum : nat -> NUMBR.


Coercion nnum : nat >-> NUMBR.


Check NUMBR.
Check 2.
Check nnum 2.


(* OPERATII ARITMETICE *)


Inductive AExp :=
| anum : nat -> AExp
(*| atroof : TROOF -> AExp*)
| ayarn : YARN -> AExp
| aplus :  AExp -> AExp -> AExp
| aminus :  AExp -> AExp -> AExp
| amul :  AExp -> AExp -> AExp
| aimp :  AExp -> AExp -> AExp
| amodul :  AExp -> AExp -> AExp.
(*| amax :  AExp -> AExp -> AExp
| amin :  AExp -> AExp -> AExp.*)

Coercion anum : nat >-> AExp.
(*Coercion atroof : TROOF >-> AExp.*)
Coercion ayarn : YARN >-> AExp.

Check anum 3.
Check (aplus (anum 2) (anum 2)). (* 2 + 2 *)

Notation " 'SUM' 'OF' A 'AN' B " := (aplus A B) (at level 50).
Notation " 'DIFF' 'OF' A 'AN' B " := (aminus A B) (at level 49).
Notation " 'PRODUKT' 'OF' A 'AN' B " := (amul A B) (at level 40).
Notation " 'QUOSHUNT' 'OF' A 'AN' B " := (aimp A B) (at level 39).
Notation " 'MOD' 'OF' A 'AN' B " := (amodul A B) (at level 38).
(*Notation " 'BIGGR' 'OF' A 'AN' B " := (amax A B) (at level 51).
Notation " 'SMALLR' 'OF' A 'AN' B " := (amin A B) (at level 52).*)
Notation " [ A ]  " := (ayarn A) (at level 50).

Check WIN.
Check ayarn.
Check ["Hello"].
Check anum 5.
Check DIFF OF 9 AN 4.


(* EXPRESII BOOLENE *)


Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp
| bnot : BExp -> BExp
| begal : AExp -> AExp -> BExp
| bdif : AExp -> AExp -> BExp
| blessthan : AExp -> AExp  -> BExp
| bgreaterthan : AExp -> AExp -> BExp
| blessthaneqto : AExp -> AExp -> BExp
| bgreaterthaneqto : AExp -> AExp -> BExp.


Notation " 'BOTH' 'OF' A 'AN' B " := (band A B) (at level 60).
Notation " 'EITHER' 'OF' A 'AN' B " := (bor A B) (at level 61).
Notation " 'NOT' A " := (bnot A) (at level 62).
Notation " 'BOTH' 'SAEM' A 'AN' B " := (begal A B) (at level 63).
Notation " 'DIFRINT' 'OF' A 'AN' B " := (bdif A B) (at level 64).
Notation " 'DIFRINT' 'IT' 'AN' 'SMALLR' 'OF' A 'AN' B " := (blessthan A B) (at level 65).
Notation " 'DIFRINT' 'IT' 'AN' 'BIGGR' 'OF' A 'AN' B " := (bgreaterthan A B) (at level 66).
Notation " 'BOTH' 'SAEM' 'IT' 'AN' 'SMALLR' 'OF' A 'AN' B " := (blessthaneqto A B) (at level 67).
Notation " 'BOTH' 'SAEM' 'IT' 'AN' 'BIGGR' 'OF' A 'AN' B " := (bgreaterthaneqto A B) (at level 68).

Check BOTH SAEM IT AN BIGGR OF 6 AN 8.

(* STATEMENTS

- definire variabile;
- atribuiri;
- concatenare pentru caractere;
- casts pentru anumite tipuri de variabile;
- comentarii;
- secvente de instructiuni;
- instructiuni conditionale cu una sau mai multe ramuri (if-else, case);
- instructiuni repetitive cu contor;
- functii si apeluri de functii

*)

Inductive Stmt :=
(*| definire_variabila_simplu : AExp -> Stmt*)
| definire_variabila_cu_o_valoare : YARN -> AExp -> Stmt
| atribuire : YARN -> AExp -> Stmt
(*| cast : AExp -> YARN -> Stmt
| comentarii : YARN -> Stmt
| concatenare_caractere : AExp -> AExp -> Stmt *)
| secventa : Stmt -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt.
(*| case : AExp -> AExp -> Stmt -> AExp -> Stmt -> Stmt  -> Stmt
| while : BExp -> AExp -> Stmt -> Stmt.
| while_cu_operatie : AExp -> AExp -> BExp -> Stmt-> Stmt 
| forr : AExp -> BExp ->AExp -> Stmt-> Stmt
| for_cu_operatie : AExp -> AExp -> BExp -> AExp -> Stmt-> Stmt 
| definire_functie : YARN -> YARN -> YARN -> Stmt -> Stmt 
| apel_functie : YARN -> AExp -> AExp -> Stmt.*)

(*
(*DEFINIRE FARA ATRIBUIRI*)
Check (definire_variabila_simplu ("H") ).
Notation " 'I' 'HAS' 'A' VAR " := (definire_variabila_simplu VAR) (at level 80).
Check I HAS A ["VAR"].

*)

(*DEFINIRE CU ATRIBUIRI*)
Check (definire_variabila_cu_o_valoare "H" 5 ).
Notation " 'I' 'HAS' 'A' A 'ITZ' B" := (definire_variabila_cu_o_valoare A B) (at level 81).
Check I HAS A "VAR" ITZ 4.



(*ATRIBUIRI*)

Notation " VAR 'R' B " := ( atribuire VAR B) (at level 82).
Check "VAR" R 3.

(*

(*CASTS*)
Check (cast (["H"]) ("TROOF") ).
Notation " 'MAEK' VAR 'A' B " := ( cast VAR B) (at level 83).
Notation " VAR 'IS' 'NOW' 'A' B  " := ( cast VAR B) (at level 83).
Check MAEK "VAR" A "TROOF". 
Check "VAR" IS NOW A "B".

(*COMENTARII*)
Check (comentarii  ("TROOF") ).
Notation " 'BTW' B " := ( comentarii B) (at level 84).
Check BTW "B". 

(* CONCATENARE CARACTERE *)
Check (concatenare_caractere ("T") ("hdjdsd")).
Notation " 'SMOOSH' VAR 'AN' B 'MKAY' " := ( concatenare_caractere VAR B) (at level 85).
Check SMOOSH "A" AN "BB" MKAY. 

*)

(* SECVENTE *)
Notation "S1 , S2" := (secventa S1 S2) (at level 98, left associativity).


(*IF THEN ELSE*)
Notation "B 'OH' 'RLY?' 'YA' 'RLY' S1 'NO' 'WAI' S2 'OIC'" := (ifthenelse B S1 S2) (at level 97).


(*

(*CASE*)
Notation " AB 'WTF?' 'OMG' B1 S1 'GTFO' 'OMG' B2 S2 'GTFO' 'OMGWTF' S3 " := (case AB B1 S1 B2 S2 S3 ) (at level 98).
Check "COLOR" WTF?
  OMG "R"
    MAEK "VAR" A "TROOF"
   GTFO
   OMG "R"
    MAEK "VAR" A "NUMBR"
   GTFO
 OMGWTF 
   "VAR" R 3.


(* while in care o variabila este incrementata *)
Notation " 'IM' 'IN' 'YR' 'WHILE' 'UPPIN' 'YR' VAR [ 'WILE' B ] S1 'IM' 'OUTTA' 'YR' 'WHILE' ":= (while VAR B S1) (at level 95).
Check IM IN YR WHILE UPPIN YR "VAR"[ WILE (BOTH SAEM IT AN BIGGR OF 6 AN 8) ]
  "VAR" IS NOW A "B"
IM OUTTA YR WHILE.


(* while in care o variabila este decrementata *)
Notation " 'IM' 'IN' 'YR' 'WHILE' 'NERFIN' 'YR' VAR [ 'WILE' B ] S1 'IM' 'OUTTA' 'YR' 'WHILE' ":= (while VAR B S1) (at level 95).
Check IM IN YR WHILE NERFIN YR "VAR"[ WILE (BOTH SAEM IT AN BIGGR OF 6 AN 8) ]
  "VAR" IS NOW A "B"
IM OUTTA YR WHILE.


(* while cu orice fel de operatie *)
Notation " 'IM' 'IN' 'YR' 'WHILE' OP 'YR' VAR [ 'WILE' B ] S1 'IM' 'OUTTA' 'YR' 'WHILE' ":= (while_cu_operatie OP VAR B S1) (at level 95).
Check IM IN YR WHILE (DIFF OF 9 AN 4) YR "VAR"[ WILE (BOTH SAEM IT AN BIGGR OF 6 AN 8) ]
  "VAR" IS NOW A "B"
IM OUTTA YR WHILE.


(* FOR in care o variabila este incrementata *)
  Notation " 'IM' 'IN' 'YR' 'FOR' 'UPPIN' 'YR' VAR [ 'TIL' B ] S1 'IM' 'OUTTA' 'YR' 'FOR' ":= (forr VAR B S1) (at level 95).
Check IM IN YR FOR UPPIN YR "VAR"[ TIL (BOTH SAEM IT AN BIGGR OF 6 AN 8) ]
  SUM OF "ALTVAR" AN 4
IM OUTTA YR FOR.


(* FOR in care o variabila este incrementata *)
  Notation " 'IM' 'IN' 'YR' 'FOR' 'NERFIN' 'YR' VAR [ 'TIL' B ] S1 'IM' 'OUTTA' 'YR' 'FOR' ":= (forr VAR B S1) (at level 95).
Check IM IN YR FOR NERFIN YR "VAR"[ TIL (BOTH SAEM IT AN BIGGR OF 6 AN 8) ]
  SUM OF "ALTVAR" AN 4
IM OUTTA YR FOR.


(* FOR cu orice fel de operatie *)
  Notation " 'IM' 'IN' 'YR' 'FOR' OP 'YR' VAR [ 'TIL' B ] S1 'IM' 'OUTTA' 'YR' 'FOR' ":= (for_cu_operatie OP VAR B S1) (at level 95).
Check IM IN YR FOR (DIFF OF 9 AN 4) YR "VAR"[ TIL (BOTH SAEM IT AN BIGGR OF 6 AN 8) ]
 SUM OF "ALTVAR" AN 4
IM OUTTA YR FOR.


(* DEFINITIE FUNCTII *)
Notation " 'HOW' 'IZ' 'I' NUME [ 'YR' PARAM1 [ 'AN' 'YR' PARAM2 ] ] S1 'IF' 'U' 'SAY' 'SO' " := (definire_functie NUME PARAM1 PARAM2 S1) (at level 97).
Check HOW IZ I "functiee" [YR "param" [ AN YR "param3" ] ]
   "VAR" IS NOW A "B"
  IF U SAY SO.


(* APEL FUNCTIE *)
Notation " 'I' 'IZ' NUME [ 'YR' PARAM1 [ 'AN' 'YR' PARAM2 ] ] 'MKAY' " := (apel_functie NUME PARAM1 PARAM2) (at level 98).
Check I IZ "functiee" [YR "param" [ AN YR "param3" ] ] MKAY.
Check I IZ "functiee" [YR "param" [ AN YR DIFF OF 9 AN 4 ] ] MKAY.




Check I HAS A ["VAR"] ITZ 4,
MAEK "VAR" A "TROOF",
"VAR" R 7,
IM IN YR WHILE (DIFF OF 9 AN 4) YR "VAR"[ WILE (BOTH SAEM IT AN BIGGR OF 6 AN 8) ]
  "VAR" IS NOW A "B"
IM OUTTA YR WHILE.


Compute DIFF OF 9 AN 4.

*)



(* OPERATII ARITMETICE *)   



(* Environment *)

Definition Env := YARN -> nat.

Scheme Equality for YARN.              
Check YARN_beq.

Definition env1 : Env :=
  fun x =>
    if (YARN_eq_dec x "VAR")
    then  10
    else 0.
Check env1.

Compute (env1 "VAR"). (* env1(sum) *)

Definition env2 : Env :=
  fun x =>
    if (YARN_eq_dec x "VAR")
    then  10
    else if (YARN_eq_dec x "N" )
         then 10
         else if (YARN_eq_dec x "I" )
              then 1
              else if (YARN_eq_dec x "SUM") 
                   then 0
                   else 0.
Check env2.

Definition update (env : Env)
           (x : YARN) (v : nat) : Env :=
  fun y =>
    if (YARN_eq_dec y "VAR")
    then v
    else if (YARN_eq_dec y "N" )
         then v
         else if (YARN_eq_dec y "I" )
              then v
              else if (YARN_eq_dec y "SUM") 
                   then v
                   else (env y).


Definition env0 := fun (var : YARN) => 0.
Compute (env0 "X").

Fixpoint aeval_fun (a : AExp) (env : Env): nat :=
  match a with
  | anum x =>  x
  | ayarn x => env x
  | aplus a1 a2 => (aeval_fun a1 env) + (aeval_fun a2 env) 
  | aminus a1 a2 => (aeval_fun a1 env) - (aeval_fun a2 env)
  | amul a1 a2 => (aeval_fun a1 env) * (aeval_fun a2 env)
  | aimp a1 a2 => (aeval_fun a1 env) / (aeval_fun a2 env)
  | amodul a1 a2 => Nat.modulo (aeval_fun a1 env) (aeval_fun a2 env)
  end.

Compute aeval_fun (SUM OF 1 AN 7 ) env1.
Compute aeval_fun (DIFF OF 12 AN 7 ) env1.
Compute aeval_fun (PRODUKT OF 1 AN 7 ) env1.
Compute aeval_fun (QUOSHUNT OF "VAR" AN 5 ) env1. (* VAR =10 *)
Compute aeval_fun (MOD OF 14 AN 7 ) env1.
Compute aeval_fun (SUM OF 20 AN "ID" ) env1.

Fixpoint beval (b : BExp) (env : Env) : bool :=
  match b with
  | btrue => true
  | bfalse => false
  | band b1 b2 => andb (beval b1 env) (beval b2 env)
  | bor b1 b2 => orb (beval b1 env) (beval b2 env)
  | bnot b' => negb (beval b' env)
  | begal a1 a2 =>  Nat.eqb (aeval_fun a1 env) (aeval_fun a2 env)
  | bdif a1 a2 =>  Nat.ltb (aeval_fun a1 env) (aeval_fun a2 env) (* PROBLEME *)
  | blessthan a1 a2 => Nat.ltb (aeval_fun a1 env) (aeval_fun a2 env)
  | bgreaterthan a1 a2 => Nat.ltb (aeval_fun a2 env) (aeval_fun a1 env)
  | blessthaneqto a1 a2 => Nat.leb (aeval_fun a1 env) (aeval_fun a2 env)
  | bgreaterthaneqto a1 a2 => Nat.leb (aeval_fun a2 env) (aeval_fun a1 env)
  end.

Compute beval ( BOTH OF btrue AN bfalse ) env1.
Compute beval ( EITHER OF btrue AN bfalse ) env1.
Compute beval ( NOT bfalse ) env1.
Compute beval (BOTH SAEM "VAR" AN 10 )env1. 
Compute beval (DIFRINT OF "VAR" AN 9 ) env1. 
Compute beval (BOTH SAEM IT AN SMALLR OF "VAR" AN 9 ) env1. 
Compute beval (BOTH SAEM IT AN BIGGR OF "VAR" AN 9 ) env1. 
Compute beval (DIFRINT IT AN SMALLR OF 12 AN 9 ) env1. 
Compute beval (BOTH SAEM IT AN BIGGR OF 19 AN 10 ) env1. 

Fixpoint execute (s : Stmt) (env : Env) : Env :=
   match s with
      | definire_variabila_cu_o_valoare var aexp => update env var (aeval_fun aexp env)
      | atribuire var aexp => update env var (aeval_fun aexp env)
      | secventa S1 S2 => execute S2 (execute S1 env)
      | ifthenelse S1 S2 S3 => if (beval S1 env)
                            then (execute S2 env)
                            else (execute S3 env)
     (*| while cond aexp s' => if (beval cond env)
                                   then aeval_fun (s', (while cond s')) env aexp
                                   else env*)
  end.

Compute (execute (I HAS A "VAR" ITZ 4) env1) "VAR".
Compute (execute ("VAR" R 3) env1) "VAR" .
Compute (execute ("N" R 6) env2) "N" .
Compute ( execute 
("N" R 10, 
"I" R 1, 
"SUM" R 0) env0 ) "VAR".

Definition init := (execute ("N" R 10, 
                             "I" R 1, 
                             "SUM" R 0) env2 ).
Compute init  "N".
Compute init "SUM".
Compute init "I".

Definition pgm :=
 "N" R 10, 
 "I" R 1, 
 "SUM" R 0,
BOTH SAEM IT AN SMALLR OF "VAR" AN 9
OH RLY?
YA RLY "SUM" R (SUM OF 1 AN "SUM") 
NO WAI  "I" R (SUM OF 1 AN "I") 
OIC.
Compute (execute pgm env0 ) "SUM".



(* Definition pgm :=
  n ::= 10 ;;
  i ::= 1 ;;
  sum ::= 0 ;; 
  If (i <=' n)  
          Then sum ::= sum +' i 
          Else i ::= i +' 1
End.

Compute (execute pgm env0 ) sum. *)

































