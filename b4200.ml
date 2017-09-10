(**
   Thibaut Balabonski @ Université Paris-Sud, 2017.
   Joé DE OLIVEIRA
**)
(* TODO
    - constantes booléennes true/false
    - message d'erreur plus instructif, donnant par exemple la position de
        l'erreur (numéro de ligne et numéro de colonne) et une indication
        sur ce qui a été rencontré/ce qui était attendu.
        Ceci peut demander d'ajouter des informations à mettre à jour
        régulièrement dans les structures de données utilisées lors des analyses
    lexicale, syntaxique ou sémantique.
    - Modifier la grammaire des expressions arithmétiques pour se rapprocher
        des règles habituelles.
*)

open Printf

(**********************************************Analyse lexicale**********************************************)

type token =
  | MAIN
  | BEGIN (* ( *)| END (* ) *)
  | IDENT of string
  | INT of int
  | VAR
  | INTEGER | BOOLEAN
  | SEMI  (* ; *)
  | PRINT | WHILE 
  | IF | ELSE
  | SET  (* := *)
  | ADD (* + *)| MULT (* * *)| SUB (* - *)| DIV (* / *)| LT (* < *) | MT (* > *) | MOD (* % *)
  | EOF | BOF  (* fin de fichier, début de fichier *)

(* Point débogage : de quoi afficher les token reconnus. *)

let token_to_string x = match x with
  | ADD     -> "ADD"
  | BEGIN   -> "BEGIN"
  | BOF     -> "START"
  | BOOLEAN -> "BOOLEAN"
  | END     -> "END"
  | EOF     -> "EOF"
  | IDENT s -> sprintf "IDENT %s" s
  | INT i   -> sprintf "INT %d" i
  | INTEGER -> "INTEGER"
  | LT      -> "LT"
  | MAIN    -> "MAIN"
  | MULT    -> "MULT"
  | PRINT   -> "PRINT"
  | SEMI    -> "SEMI"
  | SET     -> "SET"
  | VAR     -> "VAR"
  | WHILE   -> "WHILE"
  | SUB     -> "SUB"
  | DIV     -> "DIV"
  | MT      -> "MT"
  | MOD     -> "MOD"
  | IF      -> "IF"
  | ELSE    -> "ELSE"

(**
   Rappel :On veut toujours reconnaître le token le plus grand possible.
**)

(* fonction pour parcours de l'entrée initiale *)      
type input_buffer = {
  input: string; (* Mot d'entrée *)
  length: int; (* Sa longueur *)
  mutable start_pos: int; (* Début du mot analysé *)
  mutable next_pos: int; (* Position courante *)
}

(* Initialisation du buffer*)
let init_buffer s = {
  input = s;
  length = String.length s;
  start_pos = 0;
  next_pos = 0;
}

(* Lire le caractère courant *)
let next_char b =
  if   b.next_pos < b.length
  then b.input.[b.next_pos]
  else '\000' (* Charactere de fin de fichier.*)

(* Faire avancer le curseur *)
let shift b = b.next_pos <- b.next_pos + 1
  
(* Marquer le début du token en cours d'analyse *)
let init_pos b = b.start_pos <- b.next_pos

(* Obtenir le token analysé *)
let current_word b =
  String.sub b.input b.start_pos (b.next_pos - b.start_pos)

(************************************ Représentation de l'automate. *****************************************)
    
let rec read_token b =
  match next_char b with
    (* Un seul caractère : on avance, et on renvoie le token correspondant. *)
    | '(' -> shift b; BEGIN
    | ')' -> shift b; END
    | '+' -> shift b; ADD
    | '*' -> shift b; MULT
    | '-' -> shift b; SUB
    | '/' -> shift b; DIV
    | '<' -> shift b; LT
    | '>' -> shift b; MT
    | '%' -> shift b; MOD
    | ';' -> shift b; SEMI
    (* Cas particulier : fin de fichier, on n'avance plus. *)
    | '\000' -> EOF
    (* Tokens potentiellement formé de plusieurs caractères : appel d'une autre fonction.
       Si besoin, on initialise le curseur de début de token à ce moment.
    *)
    | ':' -> shift b; read_eq b
    | c when 'a' <= c && c <= 'z'|| 'A' <= c && c <= 'Z' -> init_pos b; shift b; read_word b
    | c when '0' <= c && c <= '9' -> init_pos b; shift b; read_int b
    (* On ignore les whitespaces *)
    | ' ' | '\n' | '\t' -> shift b; read_token b
    (* Tout autre caractère est une erreur. *)
    | c   -> failwith (Printf.sprintf "Unrecognized character: %c" c)

(******************** Fonctions auxiliaires correspondant aux autres états de l'automate.********************)

(* Reconnaissance du token SET *)
and read_eq b =
  match next_char b with
    (* On attend := *)
    | '=' -> shift b; SET
    (* Sinon échec *)
    | c   -> failwith (Printf.sprintf "Unrecognized character: %c" c)

(* Reconnaissance d'un entier *)
and read_int b =
  match next_char b with
    (* Tant qu'on lit des chiffres, on avance et on continue avec le même état *)
    | c when '0' <= c && c <= '9' -> shift b; read_int b
    (* Sinon on renvoie l'entier reconnu, et on préserve le prochain caractère. *)
    | _ -> INT (int_of_string (current_word b))
      
(* Lecture d'un mot *)
and read_word b =
  match next_char b with
    | c when 'a' <= c && c <= 'z' -> shift b; read_word b
    | _ -> (match current_word b with
	(* On commence par vérifier si le mot est un mot-clé. *)
	| "main" -> MAIN
	| "var" -> VAR
	| "integer" -> INTEGER
	| "boolean" -> BOOLEAN
	| "print" -> PRINT
	| "while" -> WHILE
	| "if" -> IF
	| "else" -> ELSE
	(* Sinon, c'est un identificateur. *)
	| id -> IDENT id
    )      

(**
   Grammaire:
   
     {main}  ←  DEBUT main ( integer x ) ( {locals} {block} ) FIN

   {locals}  ←  ε
             |  {local} ; {locals}

    {local}  ←  var {typ} {id}

      {typ}  ←  integer
             |  boolean

    {block}  ←  ε
             |  {instr} ; {block}

    {instr}  ←  id := {expr}
             |  while {expr} ( {block} )
             |  print ( {expr} )
             |  if {expr} ( {block} )
             |  if {expr} ( {block} ) else ( {block} )

     {expr}  ←  ( {expr} )
             |  n  {opexpr}
             |  id {opexpr}

   {opexpr}  ← ε
             | {op} {expr}

       {op}  ←  +
             |  *
             |  <
             |  >
             |  -
             |  /
*)

(**
   Syntaxe abstraite
   -----------------

   On définit d'abord une structure de 'table de symboles', qui regroupe les
   informations utiles relatives aux différentes variables.

   Le type de la structure de données est ['a Symb_Tbl.t]
   On a notamment accès aux fonctions :
   [Symb_Tbl.add   : string -> 'a -> 'a Symb_Tbl.t -> 'a Symb_Tbl.t]
   [Symb_Tbl.find  : string -> 'a Symb_Tbl.t -> 'a]
   [Symb_Tbl.empty : 'a Symb_Tbl.t]
   Voir [Map.Make] dans la documentation Caml.
*)
module Symb_Tbl = Map.Make(String)

(**
   On définit ensuite la syntaxe abstraite elle-même, sous la forme de plusieurs
   type inductifs Caml.
   Ceci consacre la forme arborescente des *arbres* de syntaxe abstraite.
*)

(* Programme principal : un ensemble de variables et un bloc de code. *)
type main = typ Symb_Tbl.t * block

(* Les types sont : les entiers et les booléens. *)
and typ = TypInteger | TypBoolean

(* Un bloc de code est une liste d'instructions. *)
and block = instruction list

(* On a trois genres d'instructions. *)
and instruction =
  | Set   of string * expression   (* [Set(id, e)]  ===  id := e;     *)
  | While of expression * block    (* [While(e, b)] ===  while e (b); *)
  | Print of expression            (* [Print(e)]    ===  print(e);    *)
  | If    of expression * block * block
  
  

(* Une expression est une constante, une variable, ou une opération binaire. *)
and expression =
  | Literal  of int
  | Location of string
  | Binop    of binop * expression * expression

and binop =
  | Add | Mult | Sub | Div | Lt | Mt | Mod

(********************* Analyse syntaxique : on utilise l'analyse récursive descendante **********************)

(* séquence implicite : on demande le token suivant à l'analyseur lexical à chaque fois qu'on en a besoin. *)
type token_buffer = {
  (* Entrée brute, d'où lire les token *)
  input: input_buffer;
  (* token courant, initialisé à [BOF] *)
  mutable next_token: token;
}

(* Retourner le token courant *)
let next_token b = b.next_token

(* Faire avancer le curseur : lire le prochain token de l'entrée *)
let shift b = b.next_token <- read_token b.input

(* Initialisation du buffer de token *)
let init_token_buffer s =
  { input = init_buffer s; next_token = BOF }

(* Vérification de l'identité du prochain terminal. *)
and expect_token t b =
  if t = next_token b
  then shift b
  else failwith  (Printf.sprintf "Syntax error : Expected %s but got %s" (token_to_string t) (token_to_string (next_token b)))

(* vérification et retour d'une variable *)
and expect_ident b =
  match next_token b with
    | IDENT s -> shift b; s
    | t    -> failwith "Ident expected"

(* Fonction principale : construit l'arbre syntaxique*)
(* {main}  ←  DEBUT main ( integer x ) ( {locals} {block} ) FIN *)
let rec parse_main b =
  (* Tout programme commence nécessairement par l'entête "main(integer x)" *)
  expect_token BOF b;
  expect_token MAIN b;
  expect_token BEGIN b;
  expect_token INTEGER b;
  let _ = expect_ident b in (* expect_indent a un retour mais ici on le jette *)
  expect_token END b;
  expect_token BEGIN b;
  (* non terminaux {locals} et {block} : appels récursifs dont on récupère les résultats. *)
  let vars = parse_locals b in
  let code = parse_block b in
  (* Enfin, on doit finir par ")" *)
  expect_token END b;
  expect_token EOF b;
  (* Une fois la règle reconnue, on renvoie la construction correspondante, de type [main].*)
  vars, code

(* {locals}  ←  ε | {local} ; {locals} *)
and parse_locals b =
  match next_token b with
    (* si on tombe sur VAR, on a une variable( donc on la parse et on recommence *)
    | VAR -> let (id, t) = parse_local b in
         expect_token SEMI b;
         let tab = parse_locals b in
         Symb_Tbl.add id t tab
    (* sinon on en a pas donc on passe la suite *)
    | _ -> Symb_Tbl.empty

(* {local}  ←  var {typ} {id} *)
and parse_local b =
  match next_token b with
    | VAR -> shift b; let t = parse_typ b in
              let id = expect_ident b in
              id, t
    | _ -> assert false

(* {block}  ←  ε | {instr} ; {block} *)
and parse_block b =
  match next_token b with
    (*si on a fini le block on se casse*)
    | END -> []
    (*sinon on continue a lire le block*)
    | _   -> let i = parse_instr b in
         expect_token SEMI b;
         let is = parse_block b in
         i :: is

(* {typ}  ←  integer |  boolean *)
and parse_typ b =
  match next_token b with
    | INTEGER -> shift b; TypInteger
    | BOOLEAN -> shift b; TypBoolean
    | t       -> failwith "Type expected"

(* {instr} ← id := {expr} | while {expr} ( {block} ) | print ( {expr} ) *)
and parse_instr b =
  match next_token b with
    | IDENT id -> shift b; expect_token SET b; let e  = parse_expr b in
                   Set(id, e)
    | WHILE    -> shift b; let e = parse_expr b in
                   expect_token BEGIN b;
                   let i = parse_block b in
                   expect_token END b;
                   While(e, i)
    | PRINT    -> shift b; expect_token BEGIN b; let e = parse_expr b in
                   expect_token END b;
                   Print(e)
    | IF       -> shift b; let e = parse_expr b in
                   expect_token BEGIN b;
                   let i = parse_block b in
                   expect_token END b;
                   let j = parse_else b in
                   If(e,i,j)
    | t        -> failwith "Bad instruction"

and parse_else b =
  match next_token b with
    | ELSE -> shift b; 
              expect_token BEGIN b;
              let i = parse_block b in
              expect_token END b;
              i
    | _  -> []
    

(* {expr} ← ( {expr} ) | n {opexpr} | id {opexpr} *)
and parse_expr b =
  match next_token b with
    | BEGIN -> shift b; let e = parse_expr b in
            let _ = expect_token END b in
            parse_op e b
    | INT i -> shift b; parse_op (Literal i) b
    | IDENT id -> shift b; parse_op (Location id) b
    | t -> failwith "Bad expression"

(* {opexpr}  ← ε | {op} {expr} *)
(*and???*)
    
(* {op}  ←  + | * | < | > | - | / *)
and parse_op e1 b =
  match next_token b with
    | ADD | MULT | DIV | SUB | LT | MT | MOD as op ->
      shift b; let e2 = parse_expr b in
           let op = match op with
         | ADD  -> Add
         | MULT -> Mult
         | LT   -> Lt
         | MT   -> Mt
         | SUB  -> Sub
         | DIV  -> Div
         | MOD  -> Mod
         | _    -> assert false
           in Binop(op, e1, e2)
    | _ -> e1
  
(*************************************************** Types **************************************************)
(*
   Règles de typage
  
   -Blocs et instructions :
   
   ∀i∈b. (Γ ⊢ i)
   -------------   Un bloc est bien typé si toutes ses instructions le sont
       Γ ⊢ b

   Γ(id) = τ        Γ ⊢ e : τ
   --------------------------   Une affectation est bien typée si les types de
          Γ ⊢ id := e           l'expression et de la variable correspondent

   Γ ⊢ e : boolean     Γ ⊢ b
   -------------------------   Une boucle est bien typée si tout son code est
        Γ ⊢ while e (b)        bien typé et si la garde est booléenne

   Γ ⊢ e : integer
   ---------------   L'affichage attend une expression de type integer
    Γ ⊢ print(e)

   -Expressions :

   ---------------   Les constantes entières sont de type integer
   Γ ⊢ n : integer

   Γ(id) = τ
   ----------   Une variable a le type indiqué par l'environnement
   Γ ⊢ id : τ

   Γ ⊢ e₁ : integer      Γ ⊢ e₂ : integer
   --------------------------------------   L'addition, la multiplication, la soustraction et la division
           Γ ⊢ e₁ + e₂ : integer            concernent uniquement les entiers

   Γ ⊢ e₁ : integer      Γ ⊢ e₂ : integer
   --------------------------------------   
           Γ ⊢ e₁ * e₂ : integer

   Γ ⊢ e₁ : integer      Γ ⊢ e₂ : integer
   --------------------------------------   
           Γ ⊢ e₁ - e₂ : integer            

   Γ ⊢ e₁ : integer      Γ ⊢ e₂ : integer
   --------------------------------------   
           Γ ⊢ e₁ / e₂ : integer

   Γ ⊢ e₁ : integer      Γ ⊢ e₂ : integer
   --------------------------------------   La comparaison produit un booléen
           Γ ⊢ e₁ < e₂ : boolean

   Γ ⊢ e₁ : integer      Γ ⊢ e₂ : integer
   --------------------------------------   
           Γ ⊢ e₁ > e₂ : boolean

   Fait intéressant : les règles de typage se traduisent assez directement
   en du code vérification le bon typage d'un programme.
*)

let check_type t1 t2 =
  if t1 <> t2
  then failwith "Type error"
    
let rec type_main (st, b) =
  let rec type_block b = List.iter type_instr b (* block -> unit *)
  and type_instr = function (* instr -> unit *)
    | Set(id, e)  -> check_type (Symb_Tbl.find id st) (type_expr e)
    | While(c, b) -> check_type TypBoolean (type_expr c); type_block b
    | Print(e)    -> check_type TypInteger (type_expr e)
    | If(a,b,c)    -> check_type TypBoolean (type_expr a);type_block b;type_block c
  and type_expr = function (* instr -> typ *)
    | Literal _ -> TypInteger
    | Location id -> Symb_Tbl.find id st
    | Binop(op, e1, e2)
      -> check_type TypInteger (type_expr e1);
	check_type TypInteger (type_expr e2);
	(match op with
	  | Add | Mult | Sub | Div | Mod -> TypInteger
	  | Lt | Mt -> TypBoolean)
  in
  type_block b


(**
   Sémantique
   ----------
   La sémantique décrit les effets de l'exécution des différents éléments
   du langage. Cela peut concerner la production d'un résultat comme la
   modification de la mémoire du système.

   De même que pour le typage on utilise des jugements et des règles de
   dérivation.

   Expressions  : ⟦e⟧ρ
   Instructions : ρ,i ⟹ ρ'
   avec
   e : expression
   ρ : état de la mémoire, associe une valeur à chaque variable
   i : instruction

   La sémantique ⟦e⟧ρ d'une expression est la valeur qu'elle produit dans
   l'état ρ.
   Ici, une valeur est nombre entier, et un environnement est une fonction
   partielle qui associe des valeurs aux identifiants. Les booléens vrai et
   faux sont associés respectivement aux valeurs 1 et 0.

          ⟦n⟧ρ = n
         ⟦id⟧ρ = ρ(id)
   ⟦e₁ op e₂⟧ρ = ⟦e₁⟧ρ ⟦op⟧ ⟦e₂⟧ρ

   À l'inverse, une instruction ne produit pas de résultat, mais peut affecter
   l'état de la mémoire. La sémantique d'une instruction est donc la manière
   dont elle modifie l'état.

         ⟦e⟧ρ = v
   --------------------------   La valeur associée à id est maintenant la
   ρ, id := e  ⟹  ρ{id ← v}    valeur calculée pour e

       ⟦e⟧ρ = v
   -------------------[Affiche v]   L'affichage ne modifie pas la mémoire
   ρ, print(e)  ⟹  ρ

   ρ₀, i ⟹ ρ₁      ρ₁, b ⟹ ρ₂   Si une instruction i est suivie par un bloc b
   -----------------------------   alors b s'exécute dans l'environnement
         ρ₀, i; b ⟹ ρ₂            produit par i

         ⟦e⟧ρ = 0
   ----------------------   Si la garde s'évalue à faux, alors la boucle n'a
   ρ, while e (b)  ⟹  ρ    pas d'effet
   
   ⟦e⟧ρ₀ = 1      ρ₀, b ⟹ ρ₁      ρ₁, while e (b) ⟹ ρ₂   Si la garde vaut vrai
   ------------------------------------------------------   alors on fait au
                 ρ₀, while e (b) ⟹ ρ₂                     moins un tour


   Comme pour les règles de typage, ces règles de sémantique se traduisent assez
   directement en du code. Ce code est celui d'un interprète du langage qui,
   partant d'un arbre de syntaxe abstraite et d'un état initial, calcule le
   nouvel état (et effectue les affichages indiqués par le programme).
*)

module State = Map.Make(String)
type state = int State.t
  
let bool_to_int op = fun v1 v2 -> if op v1 v2 then 1 else 0

(* [eval_main: main -> unit] *)
let rec eval_main (_, b) x =
  eval_block (State.singleton "x" x) b

(* [eval_block: state -> block -> state] *)
and eval_block env = function
  | []   -> env
  | i::b -> let env1 = eval_instruction env i in
        eval_block env1 b

(* [eval_instruction: state -> instruction -> state] *)
and eval_instruction env = function
  | Set (id, e) -> State.add id (eval_expression env e) env
  | While (c, b) as iw -> if eval_expression env c <> 0
                          then let env = eval_block env b in
                          eval_instruction env iw
                          else env
  | Print (e) -> Printf.printf "%c" (char_of_int (eval_expression env e)); env
  | If (a,b,c) -> if (eval_expression env a <> 0)
                  then (eval_block env b)
                  else (eval_block env c)
                  

(* [eval_expression: state -> expression -> int] *)
and eval_expression env = function
  | Literal i -> i
  | Location id -> State.find id env
  | Binop(op, e1, e2) -> 
    let v1 = eval_expression env e1 in
    let v2 = eval_expression env e2 in
    let op = match op with
        | Add  -> ( + )
        | Mult -> ( * )
        | Lt   -> bool_to_int ( < )
        | Sub  -> ( - )
        | Div  -> ( / )
        | Mt   -> bool_to_int ( > )
        | Mod  -> ( mod )
        in
    op v1 v2


(*DIRTY*DIRTY*DIRTY*DIRTY*DIRTY*DIRTY*DIRTY*DIRTY*DIRTY*DIRTY*)
let testToken s =
    let x= init_buffer s in
    Printf.printf "TOKENS : \n BOF\n";
    while(1=1) do
     let token = (token_to_string (read_token x)) in
     if (token="EOF") then (Printf.printf " EOF \n"; failwith "LexParsingDone")
     else Printf.printf " %s \n"  (token)
    done

(* Point débogage : un afficheur pour la syntaxe abstraite. *)
(*
let print_typ = function
  | TypInteger -> "integer"
  | TypBoolean -> "boolean"

let print_symb_tbl tbl =
  Symb_Tbl.fold (fun v i s ->
    (sprintf "  var %s %s;\n" (print_typ i) v) ^ s
  ) tbl ""

let print_literal i = sprintf "%d" i
let print_location id = id
let print_binop = function
  | Add  -> "+"
  | Mult -> "*"
  | Lt   -> "<"
  | Sub  -> "-"
  | Div  -> "/"
  | Mt   -> ">"
let rec print_expr = function
  | Literal lit -> print_literal lit
  | Location id -> print_location id
  | Binop(op, e1, e2) -> sprintf "( %s %s %s )" (print_expr e1) (print_binop op) (print_expr e2)

let offset o = String.make (2*o) ' '
let rec print_block o = function
  | [] -> ""
  | i::b -> (offset o) ^ (print_instr o i) ^ ";\n" ^ (print_block o b)
and print_instr o = function
  | Set(id, e) -> sprintf "%s := %s" id (print_expr e)
  | While(e, b) -> sprintf "while %s (\n%s%s)" (print_expr e) (print_block (o+1) b) (offset o)
  | Print(e) -> sprintf "print(%s)" (print_expr e)

let print_main (tbl, b) = sprintf "main(integer x) (\n%s%s)\n" (print_symb_tbl tbl) (print_block 1 b)
*)
    
(* Test final : interprétation du programme donné au début. *)
let main s x =
  let b = init_token_buffer s in
  let p = parse_main b in
  eval_main p x


(*(*test IF ESLE*)
let prog = " main(integer x) (
             var integer j;
             j := 56;
             print(j);
             print(j/2);
             print((j%2)+50);
             j := j+1;
             print((j%2)+50);
             
             if (10 < j) (print(46);j := j+1;)
             else        (print(56);j := j+1;);)
             "
*)

let prog = "main(integer x) (
     var integer i;
     var integer j;
     var boolean continue;

     continue := 1 < 2;
     i := 0;

     while continue (
       j := 0;
       while ((i*i) + (j*j)) < (x*x) (
         
         print(46);
         print(32);
         j := j+1;
       );
       continue := 0 < j;
       while (x+1) > j (
         if (j%2) > 0 (print(36);)
         else(print(38););
         print(32);
         j := j+(1*(2-1));
       );
       print(10);
       i := i+1;
       
     );
   )"



(*test des tokens*)
(*let _ = testToken prog*)


let _ = main prog 36

(*
   Plan pour la suite du cours :

   ACTE I. La compilation sans peine
   - Cours 1 -> Représentations intermédiaires et génération de code assembleur MIPS
   - Cours 2 -> Analyse lexicale, analyse syntaxique ascendante, résolution des conflits
   - Cours 3 -> Analyse de flot de données et optimisations
   - Cours 4 -> Coloration de graphes et allocation de registres
   Résultat : un langage source rudimentaire, mais un compilateur déjà évolué.

   ACTE II. La compilation ordinaire
   - Cours 1 -> Fonctions, variables locales, et pile d'appel
   - Cours 2 -> Structures de données et gestion de la mémoire
   - Cours 3 -> Sémantique
   - Cours 4 -> Typage simple
   Résultat : un compilateur pour un langage impératif raisonnable.

   ACTE III. La compilation héroïque
   - Cours 1 -> Exceptions
   - Cours 2 -> Fonctions emboîtées, fonctions d'ordre supérieur
   - Cours 3 -> Classes, objets, héritage, liaison dynamique
   - Cours 4 -> Typage avancé : polymorphisme et inférence
   Résultat : un compilateur pour un langage riche.
*)
