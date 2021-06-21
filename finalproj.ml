(* Q0  : Get familiar with the external syntax of MiniML *)
let parse_tests : (string * (string, exp) either) list = [
    (* Provide your tests for the parser *)
  ("1;", Right (Int 1));
  ("1", Left ("Expected SEMICOLON token"));
  ("true;", Right (Bool true));
    
]


let free_vars_tests : (exp * name list) list = [
  (Int 10, []);
  (Var "x",["x"]);
]

(* Q1  : Find the free variables in an expression *)
let rec free_vars (e : exp) : name list = match e with 
  |  Int _ | Bool _-> []
  |  If (e1,e2,e3) -> union_list [free_vars e1; free_vars e2 ; free_vars e3] 
  |  Primop (_,exp_list) -> union_list (List.map free_vars exp_list)
  |  Tuple exp_list -> union_list (List.map free_vars exp_list)
  |  Fn (name,_,exp) |  Rec (name,_,exp)  -> delete [name] (free_vars exp)
  |  Apply (e1,e2) -> union_list [free_vars e1; free_vars e2]
  |  Var name -> [name]
  |  Anno (exp,typ) -> free_vars exp 
  |  Let (dec_list, exp) -> match dec_list with
    | [] -> free_vars exp
    | h ::t -> match h with 
      | Val (expr,name) | ByName (expr,name)->
                                  (*FV(expr) union (FV(rest) \ name ) *)
          union_list [free_vars expr; 
                      delete [name] (free_vars (Let (t,exp) ))]
      | Valtuple (expr,name_list) -> 
          union_list [free_vars expr;
                      delete name_list (free_vars exp)]
                                  
                        
let unused_vars_tests : (exp * name list) list = [
  (Let ([Val (Int 3,"x")], Int 4), ["x"]);
  (Let ([Val (Bool true, "x")], Let ([Val (Int 4,"y")], Primop (Plus,[Var "x"; Int 5]))  ) , ["y"]);
]

(* Q2  : Check variables are in use *)
let rec unused_vars (e : exp) : name list = match e with
  | Fn (name,_,exp) -> if member name (free_vars exp) 
      then unused_vars exp 
      else name :: unused_vars exp 
  | Rec (name,_,exp) -> unused_vars exp
  | Let (dec_list, exp) -> (match dec_list with
      | [] -> unused_vars exp
      | h ::t -> match h with 
        | Val (expr,name) | ByName (expr,name)->
            if member name (free_vars (Let (t,exp)))
            then unused_vars expr @ unused_vars (Let (t,exp))
            else name :: unused_vars expr @ unused_vars (Let (t,exp))
        | Valtuple (expr,name_list) -> 
            let free = free_vars exp in 
                                    (*filter out the unused ones*)
            (List.filter (fun x->not(member x free)) name_list)
            @unused_vars expr @ unused_vars exp )
  | Int _ | Bool _ | Var _-> []
  | If (e1,e2,e3) -> unused_vars e1 @ unused_vars e2 @ unused_vars e3
  | Primop (_,exp_list) | Tuple exp_list-> List.concat (List.map unused_vars exp_list)
  | Anno (exp,_) -> unused_vars exp
  | Apply (e1,e2)  -> unused_vars e1 @ unused_vars e2


let subst_tests : (((exp * name) * exp) * exp) list = [
]
(*Q3 helper function that replaces all occurences of x with fresh_var*)

let rec rename_var (e:exp) (x:name) (fresh_var:name) : exp = 
  (match e with
   | Int y -> Int y 
   | Bool y -> Bool y 
   | If (e1,e2,e3) -> If (rename_var e1 x fresh_var,
                          rename_var e2 x fresh_var,
                          rename_var e3 x fresh_var)
   | Primop (op,exp_list) -> Primop (op, List.map (fun exp -> rename_var exp x fresh_var) exp_list)
   | Tuple (exp_list) -> Tuple (List.map (fun exp -> rename_var exp x fresh_var) exp_list)
   | Fn (name,typ,exp) -> if name = x then 
         Fn (fresh_var,typ, rename_var exp x fresh_var)
       else
         Fn (name,typ,rename_var exp x fresh_var) 
   | Rec (name,typ,exp) -> if name = x then 
         Rec (fresh_var,typ, rename_var exp x fresh_var)
       else
         Rec (name,typ,rename_var exp x fresh_var)
   | Let (dec_list,exp) ->  let rename_dec (dec : dec) (x:name) (fresh_var:name) : dec = 
                              match dec with
                              |Val(expr,name) -> if name = x then Val(rename_var expr x fresh_var,fresh_var)
                                  else  Val(rename_var expr x fresh_var,name)
                              |ByName(expr,name) -> if name = x then ByName(rename_var expr x fresh_var,fresh_var)
                                  else  ByName(rename_var expr x fresh_var,name)
                              |Valtuple (expr,name_list) ->
                                  Valtuple(rename_var expr x fresh_var,
                                           List.map (fun name -> if name=x then fresh_var else name ) name_list)
       in 
       Let (List.map (fun dec -> rename_dec dec x fresh_var) dec_list , rename_var exp x fresh_var )
   | Apply (e1,e2) -> Apply (rename_var e1 x fresh_var,rename_var e2 x fresh_var)
   | Var name -> if name = x then Var fresh_var else Var name 
   | Anno (exp,typ) -> Anno (rename_var exp x fresh_var, typ)
  )

(* Q3  : Substitute a variable *)
let rec subst ((e', x) : exp * name) (e : exp) : exp =
  (*this helper goes through everything in a dec list and make adjustments to the original let exp to avoid variable capture*)
  let rec dec_helper (ds:dec list) (e2:exp) (cont: dec list -> dec list): exp = (match ds with
      | [] -> Let (cont [], e2) 
      | h::t -> (match h with 
          |Val (expr,name) -> 
              if name = x 
              then 
                let new_h = Val(subst(e',x) expr,name) in 
                dec_helper t e2 (fun acc -> cont (new_h::acc))
              else if member name (free_vars e')
              then 
                let new_name = fresh_var name in 
                let new_let = rename_var (Let (ds,e2)) name new_name in 
                let (new_ds,new_e2) = (match new_let with 
                    | Let (ds',e2') -> (ds',e2')
                    | _ -> raise (Stuck "susbtitution error in dec_helper when eliminating variable capture" ) ) in 
                dec_helper new_ds new_e2 cont 
              else 
                let new_h = Val (subst (e',x) expr, name ) in 
                dec_helper t (subst (e',x) e2) (fun acc -> cont (new_h::acc))

          |ByName (expr,name) ->  if name = x 
              then 
                let new_h = ByName(subst(e',x) expr,name) in 
                dec_helper t e2 (fun acc -> cont (new_h::acc))
              else if member name (free_vars e')
              then 
                let new_name = fresh_var name in 
                let new_let = rename_var (Let (ds,e2)) name new_name in 
                let (new_ds,new_e2) = (match new_let with 
                    | Let (ds',e2') -> (ds',e2')
                    | _ -> raise (Stuck "susbtitution error in dec_helper  when eliminating variable capture" ) ) in 
                dec_helper new_ds new_e2 cont 
              else 
                let new_h = ByName (subst (e',x) expr, name ) in 
                dec_helper t (subst (e',x) e2) (fun acc -> cont (new_h::acc))

          |Valtuple(expr,name_list) ->
              try 
                let name = List.find (fun name -> member name (free_vars e')) name_list in 
                let new_name = fresh_var name in 
                let new_let = rename_var (Let (ds,e2)) name new_name in 
                let (new_ds,new_e2) = (match new_let with
                    | Let (ds',e2') -> (ds',e2')
                    | _ -> raise (Stuck "susbtitution error in dec_helper when eliminating variable capture" ) ) in 
                dec_helper new_ds new_e2 cont
              with Not_found -> 
                try let name = List.find (fun name -> name = x) name_list in 
                  let new_h = Valtuple (subst (e',name) expr,name_list) in 
                  dec_helper t e2 (fun acc -> cont (new_h ::acc))
                with Not_found ->  
                  let new_h = Valtuple (subst (e',x) expr,name_list) in
                  dec_helper t (subst (e',x) e2)  (fun acc -> cont (new_h ::acc))
        )) in 
  match e with
  | Var y ->
      if x = y then
        e'
      else
        Var y
  | Int _ | Bool _ -> e
  | Primop (po, es) -> Primop (po, List.map (subst (e', x)) es)
  | If (e1, e2, e3) -> If (subst (e', x) e1, subst (e', x) e2, subst (e', x) e3)
  | Tuple es -> Tuple (List.map (subst (e', x)) es)
  | Anno (e, t) -> Anno (subst (e', x) e, t)
  | Let (ds, e2) -> if ds = [] then subst (e',x) e2 else dec_helper ds e2 (fun y -> y)
  | Apply (e1, e2) -> Apply (subst (e',x) e1, subst (e',x) e2)
  | Fn (y, t, e) -> if x = y then Fn (y,t,e)
      else if member y (free_vars e')
      then 
        let new_y = fresh_var y in 
        let renamed_Fn = rename_var (Fn(y,t,e)) y new_y in
        subst (e',x) renamed_Fn
      else Fn (y,t,subst (e',x) e)
  | Rec (y, t, e) -> if x = y then Rec (y,t,e) 
      else if member y (free_vars e') 
      then 
        let new_y = fresh_var y in
        let renamed_Rec = rename_var (Rec(y,t,e)) y new_y in 
        subst (e',x) renamed_Rec 
      else  Rec (y,t,subst (e',x) e)


let eval_tests : (exp * exp) list = [
]

(* Q4  : Evaluate an expression in big-step *)
let rec eval : exp -> exp =
  (* do not change the code from here *)
  let bigstep_depth = ref 0 in
  fun e ->
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "eval (" ^ Print.exp_to_string e ^ ")\n");
    incr bigstep_depth;
  (* to here *)
    let result =
      match e with
      | Int _ | Bool _ -> e
      | Tuple es -> Tuple (List.map eval es)
      | If (e1, e2, e3) ->
          begin match eval e1 with
            | Bool b ->
                if b then
                  eval e2
                else
                  eval e3
            | _ -> stuck "Condition for if expression should be of the type bool"
          end
      | Anno (e, _) -> eval e     (* types are ignored in evaluation *)
      | Var x -> stuck ("Free variable \"" ^ x ^ "\" during evaluation")

      | Fn (x, t, e) -> Fn (x, t, e)
      | Apply (e1, e2) ->(match eval e1, eval e2 with 
          | Fn (x,t,e),  v2 -> eval (subst (v2,x) e)
          |  _ -> stuck ("e1 is not a function")
        )
                      
      | Rec (f, t, e) -> eval (subst (Rec(f,t,e),f) e)

      | Primop (And, es) -> (match es with 
          | e1::e2 :: []-> (match eval e1 with  
              | Bool b -> if b then eval e2 else Bool false
              | _ -> stuck ("e1 must have type bool in order to evaluate Primop And"))
          | _ -> stuck ("Primop And only allows two arguments")) 
      | Primop (Or, es) -> (match es with 
          | e1 ::e2 :: [] -> (match eval e1 with
              | Bool b -> if b then Bool true else eval e2 
              | _ -> stuck ("e1 must have type bool in order to evaluate Primop Or"))
          | _ -> stuck ("Primop Or only allows two arguments"))
      | Primop (op, es) ->
          let vs = List.map eval es in
          begin match eval_op op vs with
            | None -> stuck "Bad arguments to primitive operation"
            | Some v -> v
          end

      | Let (ds, e) -> (match ds with
          | [] -> eval e 
          | h :: t -> (match h with 
              | Val (e1,x) -> let v1 = eval e1 in
                  eval (subst (v1,x) (Let(t,e)) )
              | ByName (e1,x) -> eval (subst (e1,x) (Let(t,e))) 
              | Valtuple (e1,xs) -> match eval e1 with 
                | Tuple vs -> if (List.length xs = List.length vs)
                    then 
                      let ls = List.combine vs xs in 
                      eval (List.fold_right subst ls (Let (t,e)))
                    else stuck ("tuple matching failed since they have different number of elements")
                | _ -> stuck ("e1 doesn't evaluate to a tuple")
                                                
            )
        )
    in
  (* do not change the code from here *)
    decr bigstep_depth;
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "result of eval (" ^ Print.exp_to_string e ^ ") = "
         ^ Print.exp_to_string result ^ "\n");
  (* to here *)
    result



let infer_tests : ((context * exp) * typ) list = [
]

(* Q5  : Type an expression *)
(* Q7* : Implement the argument type inference
         For this question, move this function below the "unify". *)
let infer (ctx : context) (e : exp) : typ = 
  let rec infer_exp ctx e =  
    let rec infer_dec (ctx:context) (dec:dec) : context = match dec with 
      | Val (expr,name)| ByName (expr,name) -> let typ = infer_exp ctx expr in Ctx [(name,typ)]
      | Valtuple (expr,name_list) ->  (match infer_exp ctx expr with  
          | TProduct typ_list -> (if List.length typ_list = List.length name_list
                                  then  let list = List.combine name_list typ_list in Ctx list
                                  else type_fail ("infer_dec failed because Valtuple doesn't match its exp"))
          | _ -> type_fail ("infer_dec failed because Valtuple doesn't match its exp"))
    in 
    let rec infer_decs (ctx:context) (ds: dec list) : context = match ds with
      | dec1::decs -> let Ctx ctx1 = infer_dec ctx dec1 in 
          let Ctx ctx2 = infer_decs (extend_list ctx ctx1) decs in 
          extend_list (Ctx ctx1) ctx2  
      | []  -> ctx
    in 
    (match e with
     | If (e1,e2,e3) -> (match infer_exp ctx e1, infer_exp ctx e2,infer_exp ctx e3 with
         | TBool,t,t' when t=t' -> t 
         | _ -> type_fail ("this if is not well-typed"))
     | Fn (x,Some t,exp) -> TArrow(t,infer_exp (extend ctx (x,t)) exp)
     | Fn (_,None,_) -> type_fail ("function type is missing, so can't infer")                
     | Tuple es -> TProduct (List.map (infer_exp ctx) es )
     | Rec(name,t,exp) -> infer_exp (extend ctx (name,t)) exp
     | Apply (e1 , e2 ) -> (match infer_exp ctx e1 , infer_exp ctx e2 with
         | TArrow (e1t1,e1t2) , e2t when e1t1 = e2t -> e1t2
         | _ -> type_fail("Apply ill-typed"))
     | Let(ds,exp) -> let Ctx ctx' = infer_decs ctx ds in infer_exp (extend_list ctx ctx') exp
     | Anno (exp,typ) -> let typ'= infer_exp ctx exp in
         if typ = typ' then typ' else type_fail ("Anno ill-typed")
     | Int _ -> TInt 
     | Bool _ -> TBool
     | Var x -> (try 
                   let t = ctx_lookup ctx x in t
                 with NotFound -> type_fail ("x does not have a type in context"))
     | Primop (op,es) -> (match op with
         | Plus | Minus | Times | Div -> (match es with 
             | e1 :: e2 :: [] -> if infer_exp ctx e1 = TInt 
                 then 
                   (if infer_exp ctx e2 = TInt 
                    then TInt 
                    else  type_fail ("+ - * / only accepts int"))
                 else type_fail ("+ - * / only accepts int")
             | _ -> type_fail ("Wrong number of args for + - * /"))
         | Equals | NotEquals | LessThan | LessEqual
         | GreaterThan | GreaterEqual ->  (match es with 
             | e1 :: e2 :: [] -> if infer_exp ctx e1 = TInt 
                 then 
                   (if infer_exp ctx e2 = TInt 
                    then TBool 
                    else  type_fail ("< <= > >= = != only accepts int"))
                 else type_fail ("< <= > >= = != only accepts int")
             | _ -> type_fail ("Wrong number of args for < <= > >= = !="))    
         | And | Or -> (match es with 
             | e1 :: e2 :: [] -> if infer_exp ctx e1 = TBool
                 then 
                   (if infer_exp ctx e2 = TBool 
                    then TBool 
                    else  type_fail ("&& || only accepts int"))
                 else type_fail ("&& || only accepts int")
             | _ -> type_fail ("Wrong number of args for && ||"))
         | Negate -> (match es with 
             | e1 :: [] -> if infer_exp ctx e1 = TInt 
                 then TInt
                 else type_fail (" ~ only accepts int")
             | _ -> type_fail ("Wrong number of args for ~")) )
  

    )  in infer_exp ctx e 


let unify_tests : ((typ * typ) * unit) list = [
]

(* find the next function for Q5 *)
(* Q6  : Unify two types *)
let unify (ty1 : typ) (ty2 : typ) : unit = (*check if a in FV(t)*)
  let rec fv (a:typ) (t:typ) :bool=   
    match t with
    | TInt | TBool -> false 
    | x when a == x -> true 
    | TArrow (t1,t2) -> fv a t1 || fv a t2
    | TProduct list -> List.exists (fv a) list
    | TVar x -> (match !x with 
        |None -> false 
        |Some typ -> fv a typ
      )

  in 
  let rec unify_rec c = (match c with
      | [] -> ()
      | (ty1,ty2) :: c' -> (match ty1, ty2 with 
          | x,y when x == y  -> unify_rec c'
          | TProduct l1, TProduct l2 when List.length l1 = List.length l2 -> unify_rec ((List.combine l1 l2) @ c')  
          | TArrow (t1,t2), TArrow (s1,s2) -> unify_rec ((t1,s1)::(t2,s2)::c')
          | TVar a, t | t, TVar a  -> 
              if not (fv ty1 t) then
                (a := Some t; unify_rec c')
              else type_fail ("not unifiable")
                      
          | _ -> type_fail ("not unifiable")
        )
    )
  in 
  let c = [(ty1,ty2)] in 
  unify_rec c 


(* Now you can play with the language that you've implemented! *)
let execute (s: string) : unit =
  match P.parse s with
  | Left s -> print_endline ("parsing failed: " ^ s)
  | Right e ->
      try
       (* first we type check the program *)
        ignore (infer (Ctx []) e);
        let result = eval e in
        print_endline ("program is evaluated to: " ^ Print.exp_to_string result)
      with
      | NotImplemented -> print_endline "code is not fully implemented"
      | Stuck s -> print_endline ("evaluation got stuck: " ^ s)
      | NotFound -> print_endline "variable lookup failed"
      | TypeError s -> print_endline ("type error: " ^ s)
      | e -> print_endline ("unknown failure: " ^ Printexc.to_string e)


(************************************************************
 *                     Tester template:                     *
 *         Codes to test your interpreter by yourself.      *
 *         You can change these to whatever you want.       *
 *                We won't grade these codes                *
 ************************************************************)
let list_to_string el_to_string l : string =
  List.fold_left
    begin fun acc el ->
      if acc = "" then
        el_to_string el
      else
        acc ^ "; " ^ el_to_string el
    end
    ""
    l
  |> fun str -> "[" ^ str ^ "]"

let run_test name f ts stringify : unit =
  List.iteri
    begin fun idx (input, expected_output) ->
      try
        let output = f input in
        if output <> expected_output then
          begin
            print_string (name ^ " test #" ^ string_of_int idx ^ " failed\n");
            print_string (stringify output ^ " <> " ^ stringify expected_output);
            print_newline ()
          end
      with
      | exn ->
          print_string (name ^ " test #" ^ string_of_int idx ^ " raised an exception:\n");
          print_string (Printexc.to_string exn);
          print_newline ()
    end
    ts

let run_free_vars_tests () : unit =
  run_test "free_vars" free_vars free_vars_tests (list_to_string (fun x -> x))

let run_unused_vars_tests () : unit =
  run_test "unused_vars" unused_vars unused_vars_tests (list_to_string (fun x -> x))

let run_subst_tests () : unit =
  run_test "subst" (fun (s, e) -> subst s e) subst_tests Print.exp_to_string

let run_eval_tests () : unit =
  run_test "eval" eval eval_tests Print.exp_to_string

(* You may want to change this to use the unification (unify) instead of equality (<>) *)
let run_infer_tests () : unit =
  run_test "infer" (fun (ctx, e) -> infer ctx e) infer_tests Print.typ_to_string

let run_unify_tests () : unit =
  run_test "unify" (fun (ty1, ty2) -> unify ty1 ty2) unify_tests (fun () -> "()")

let run_all_tests () : unit =
  run_free_vars_tests ();
  run_unused_vars_tests ();
  run_subst_tests ();
  run_eval_tests ();
  run_infer_tests ();
  run_unify_tests ()
