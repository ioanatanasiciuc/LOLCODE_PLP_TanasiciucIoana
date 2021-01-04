Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.

(* TIP BOOL *)

Inductive bool : Set := true : bool | false : bool.

Inductive TROOF :=
| ttrue : bool -> TROOF
| tfalse : bool -> TROOF.

Coercion ttrue : bool >-> TROOF.

Check tfalse false.

Notation " 'WIN' " := (ttrue true) (at level 50).
Notation " 'FAIL' " := (tfalse false) (at level 50).

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
| anum : NUMBR -> AExp
| atroof : TROOF -> AExp
| ayarn : YARN -> AExp
| aplus :  AExp -> AExp -> AExp
| aminus :  AExp -> AExp -> AExp
| amul :  AExp -> AExp -> AExp
| aimp :  AExp -> AExp -> AExp
| amodul :  AExp -> AExp -> AExp
| amax :  AExp -> AExp -> AExp
| amin :  AExp -> AExp -> AExp.

Coercion anum : NUMBR >-> AExp.
Coercion atroof : TROOF >-> AExp.
Coercion ayarn : YARN >-> AExp.

Check anum 3.
Check (aplus (anum 2) (anum 2)). (* 2 + 2 *)

Notation " 'SUM' 'OF' A 'AN' B " := (aplus A B) (at level 50).
Notation " 'DIFF' 'OF' A 'AN' B " := (aminus A B) (at level 49).
Notation " 'PRODUKT' 'OF' A 'AN' B " := (amul A B) (at level 40).
Notation " 'QUOSHUNT' 'OF' A 'AN' B " := (aimp A B) (at level 39).
Notation " 'MOD' 'OF' A 'AN' B " := (amodul A B) (at level 38).
Notation " 'BIGGR' 'OF' A 'AN' B " := (amax A B) (at level 51).
Notation " 'SMALLR' 'OF' A 'AN' B " := (amin A B) (at level 52).
Notation " [ A ]  " := (ayarn A) (at level 50).

Check WIN.
Check atroof (WIN).
Check ayarn.
Check ["Hello"].
Check anum 5.
Check DIFF OF 9 AN 4.
Check MOD OF (atroof (WIN)) AN 5.


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
| definire_variabila_simplu : AExp -> Stmt
| definire_variabila_cu_o_valoare : AExp -> AExp -> Stmt
| atribuire : AExp -> AExp -> Stmt
| cast : AExp -> AExp -> Stmt
| comentarii : AExp -> Stmt
| concatenare_caractere : AExp -> AExp -> Stmt
| secventa : Stmt -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| case : AExp -> AExp -> Stmt -> AExp -> Stmt -> Stmt  -> Stmt
| while : AExp -> BExp -> Stmt-> Stmt
| while_cu_operatie : AExp -> AExp -> BExp -> Stmt-> Stmt 
| forr : AExp -> BExp -> Stmt-> Stmt
| for_cu_operatie : AExp -> AExp -> BExp -> Stmt-> Stmt 
| definire_functie : YARN -> YARN -> YARN -> Stmt -> Stmt 
| apel_functie : YARN -> AExp -> AExp -> Stmt.


Check (definire_variabila_simplu ("H") ).
Notation " 'I' 'HAS' 'A' VAR " := (definire_variabila_simplu VAR) (at level 80).
Check I HAS A ["VAR"].


Check (definire_variabila_cu_o_valoare ("H") 5 ).
Notation " 'I' 'HAS' 'A' A 'ITZ' B" := (definire_variabila_cu_o_valoare A B) (at level 81).
Check I HAS A ["VAR"] ITZ 4.
Check I HAS A ["VAR"] ITZ (WIN).


Check (atribuire (["H"]) (WIN) ).
Notation " VAR 'R' B " := ( atribuire VAR B) (at level 82).
Check "VAR" R 3.

Check (cast (["H"]) ("TROOF") ).
Notation " 'MAEK' VAR 'A' B " := ( cast VAR B) (at level 83).
Notation " VAR 'IS' 'NOW' 'A' B  " := ( cast VAR B) (at level 83).
Check MAEK "VAR" A "TROOF". 
Check "VAR" IS NOW A "B".

Check (comentarii  ("TROOF") ).
Notation " 'BTW' B " := ( comentarii B) (at level 84).
Check BTW "B". 


Check (concatenare_caractere ("T") ("hdjdsd")).
Notation " 'SMOOSH' VAR 'AN' B 'MKAY' " := ( concatenare_caractere VAR B) (at level 85).
Check SMOOSH "A" AN "BB" MKAY. 

Notation "S1 , S2" := (secventa S1 S2) (at level 98, left associativity).

Notation "B 'OH' 'RLY?' 'YA' 'RLY' S1 'NO' 'WAI' S2 'OIC'" := (ifthenelse B S1 S2) (at level 97).

Notation " AB ',' 'WTF?' 'OMG' B1 S1 'GTFO' 'OMG' B2 S2 'GTFO' 'OMGWTF' S3 " := (case AB B1 S1 B2 S2 S3 ) (at level 98).


Check "COLOR" , WTF?
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
  "VAR" IS NOW A "B"
IM OUTTA YR FOR.


(* FOR in care o variabila este incrementata *)
  
Notation " 'IM' 'IN' 'YR' 'FOR' 'NERFIN' 'YR' VAR [ 'TIL' B ] S1 'IM' 'OUTTA' 'YR' 'FOR' ":= (forr VAR B S1) (at level 95).

Check IM IN YR FOR NERFIN YR "VAR"[ TIL (BOTH SAEM IT AN BIGGR OF 6 AN 8) ]
  "VAR" IS NOW A "B"
IM OUTTA YR FOR.


(* FOR cu orice fel de operatie *)
  
Notation " 'IM' 'IN' 'YR' 'FOR' OP 'YR' VAR [ 'TIL' B ] S1 'IM' 'OUTTA' 'YR' 'FOR' ":= (for_cu_operatie OP VAR B S1) (at level 95).

Check IM IN YR FOR (DIFF OF 9 AN 4) YR "VAR"[ TIL (BOTH SAEM IT AN BIGGR OF 6 AN 8) ]
  "VAR" IS NOW A "B"
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







