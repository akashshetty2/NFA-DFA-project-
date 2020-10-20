open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

let option_convert x = Some x 
(****************)
(* Part 1: NFAs *)
(****************)

let rec move_helper target trans lst return_list = 
  match lst with 
  |[] -> return_list
  |(curr, move, next) :: t -> if (curr = target && trans = move) then (move_helper target trans t (insert next return_list)) else (move_helper target trans t return_list)
  
let rec move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
  match qs with 
  |[] -> [] 
  |h :: t -> (union (move_helper h s nfa.delta []) (move nfa t s)) 

let rec e_closure_helper target lst return_list = 
  match lst with 
  |[] -> return_list 
  |(curr, move, next) :: t -> if (curr = target && move = None) then (union (e_closure_helper target t (insert next return_list)) (e_closure_helper next lst [next])) else (e_closure_helper target t return_list)
  
let rec e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
  match qs with 
  |[] -> [] 
  |h :: t -> (union (e_closure_helper h nfa.delta [h]) (e_closure nfa t)) 

(* let delta_iterate curr delta target = 
  match delta with 
  |[] -> None 
  |(start, move, next) :: t -> if (curr = start && move = target) then next else (delta curr t target) *)

(* let accept_helper string delta start = 
  match string with 
  |[] -> True 
  |h :: t -> if (delta_iterate start) *)

(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let rec new_states_helper sigma qs nfa = 
  match sigma with 
  |[] -> [] 
  |h :: t -> (e_closure nfa (move nfa qs (option_convert h))) :: (new_states_helper t qs nfa) 

let rec new_trans_helper lst alpha qs = 
  match lst, alpha with 
  |[], [] -> []
  |h :: t, alphah :: alphat -> (qs, (option_convert alphah), h) :: (new_trans_helper t alphat qs) 

let rec new_finals_helper states qs = 
  match states with 
  |[] -> [] 
  |h :: t -> if (elem h qs) then [qs] else (new_finals_helper t qs) 

let rec new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list = (new_states_helper nfa.sigma qs nfa) 

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list = (new_trans_helper (new_states nfa qs) nfa.sigma qs)

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list = (new_finals_helper nfa.fs qs)

let rec dfa_elements nfa init return_list = 
  match init with 
  |[] -> return_list 
  |[(start, trans, dest)] :: t -> if ((elem dest return_list) || dest = []) then (dfa_elements nfa t return_list) else (dfa_elements nfa (insert (new_trans nfa dest) t) (insert dest return_list))

let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
    (work: 'q list list) : ('q list, 's) nfa_t =
    match work with 
    |[] -> dfa 
    |h :: t -> if (h != []) then (let dfa_return = 
              { 
                sigma = dfa.sigma ;
                qs = (insert h dfa.qs) ;
                q0 =  dfa.q0 ; 
                fs = (union (new_finals nfa h)  dfa.fs);
                delta = (union (new_trans nfa h)  dfa.delta) 
              } in 
                let  x = minus (union (new_states nfa h) (t)) dfa_return.qs in (nfa_to_dfa_step nfa dfa_return x))
                else (nfa_to_dfa_step nfa dfa t)
              

let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t = 
  let start = [(e_closure nfa [nfa.q0])] in 
  let dfa = { 
    sigma = nfa.sigma ; 
    qs = [(e_closure nfa [nfa.q0])] ;
    q0 = (e_closure nfa [nfa.q0]) ; 
    fs = [] ; 
    delta = [] 
  } in (nfa_to_dfa_step nfa dfa start) 
  

let rec accept_helper nfa curr str_arr = 
  if (curr = []) then [] else 
  match str_arr with 
  |[] -> curr 
  |h :: t -> (accept_helper nfa (move nfa curr (option_convert h)) t)

  (*  *)

let accept (nfa: ('q,char) nfa_t) (s: string) : bool = 
  let dfa = (nfa_to_dfa nfa) in 
    match (accept_helper dfa [dfa.q0] (explode s)) with 
    |[] -> false
    |h :: t -> (elem h dfa.fs) 