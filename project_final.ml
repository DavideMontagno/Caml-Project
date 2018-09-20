 type ide = string;;
    type exp = 
      Eint of int 
      | Ebool of bool 
      | Den of ide
      | Prod of exp * exp
      | Sum of exp * exp
      | Diff of exp * exp
      | Eq of exp * exp
      | Minus of exp
      | Iszero of exp
      | Or of exp * exp
      | And of exp * exp
      | Not of exp
      | Ifthenelse of exp * exp * exp
			| LessThan of exp * exp
      | Let of ide * exp * exp      
      | Fun of ide list * exp
      | Appl of exp * exp list
      | Rec of ide * exp
      | Etup  of  tuple 
      | Pipe  of  tuple 
			| ApplyManyTimes of exp * exp
			| ApplyPipe of exp * exp
      | ManyTimes of  int * exp 
      and tuple = Nil 
      |Seq of exp * tuple  ;;




 type 't env = string -> 't 
     exception WrongBindlist 
     let emptyenv(x) = function y -> x
     let applyenv(x,y) = x y
     let bind((r: 'a env) , (l:string),  (e:'a)) = 
          function lu -> if lu = l then e else applyenv(r,lu)
     let rec bindlist(r, il, el) = match (il,el) with
        | ([],[]) -> r
  | i::il1, e::el1 -> bindlist (bind(r, i, e), il1, el1)
  | _ -> raise WrongBindlist;;


type eval =    
     | Int of int 
     | Bool of bool 
     | Unbound
     | Funval of efun 
     | PipeVal of efun list (*lista di funzioni valutate*)
     | EtupVal of eval list (* lista di espressioni valutate*)
		 | ManyTimesVal of int * exp * (eval env)
and efun = exp * (eval env);;

 let typecheck (x, y) =
      match x with
      | "int" ->
    (match y with 
    |  Int(u) -> true
    | _ -> false)
      | "bool" ->
    (match y with 
    |  Bool(u) -> true
    | _ -> false)
      | _ -> failwith ("errore di tipo")
      
    let minus x =
      if typecheck("int",x) 
      then 
      (match x with
      | Int(y) -> Int(-y) )
      else 
      failwith ("errore di tipo")
      
    let iszero x =
      if typecheck("int",x) 
      then 
      (match x with
      | Int(y) -> Bool(y=0) )
      else 
      failwith ("errore di tipo")
      
    let equ (x,y) =
      if typecheck("int",x) & typecheck("int",y) 
      then 
    (match (x,y) with
    | (Int(u), Int(w)) -> Bool(u = w))
      else failwith ("errore di tipo")
      
    let plus (x,y) =
      if typecheck("int",x) & typecheck("int",y) 
      then 
    (match (x,y) with
    | (Int(u), Int(w)) -> Int(u+w))
      else failwith ("errore di tipo")
      
    let diff (x,y) =
      if typecheck("int",x) & typecheck("int",y) 
      then 
    (match (x,y) with
    | (Int(u), Int(w)) -> Int(u-w))
      else failwith ("errore di tipo")
      
    let mult (x,y) =
      if typecheck("int",x) & typecheck("int",y) 
      then 
    (match (x,y) with
    | (Int(u), Int(w)) -> Int(u*w))
      else failwith ("errore di tipo")
      
    let et (x,y) =
      if typecheck("bool",x) & typecheck("bool",y) 
      then 
    (match (x,y) with
    | (Bool(u), Bool(w)) -> Bool(u & w))
      else failwith ("errore di tipo")
      
    let vel (x,y) =
      if typecheck("bool",x) & typecheck("bool",y) 
      then 
    (match (x,y) with
    | (Bool(u), Bool(w)) -> Bool(u or w))
      else failwith ("errore di tipo")
      
    let non x =
      if typecheck("bool",x) 
      then 
      (match x with
      | Bool(y) -> Bool(not y) )
      else failwith ("errore di tipo");;
		
		let lessthan (x,y) = if typecheck("int",x) & typecheck("int",y) then
													match (x,y) with
													| (Int(u),Int(w)) -> Bool(u<w)
												 else failwith ("errore di tipo")



			
let rec sem ((e:exp), (r:eval env)) =
      match e with
      | Eint(n) -> Int(n)
      | Ebool(b) -> Bool(b)
      | Den(i) -> applyenv(r,i)
      | Iszero(a) -> iszero(sem(a, r))
      | Eq(a,b) -> equ(sem(a, r), sem(b, r))
      | Prod(a,b) ->  mult (sem(a, r), sem(b, r))
      | Sum(a,b) ->  plus (sem(a, r), sem(b, r))
      | Diff(a,b)  ->  diff (sem(a, r), sem(b, r))
      | Minus(a) ->  minus(sem(a, r))
      | And(a,b) ->  et (sem(a, r), sem(b, r))
      | Or(a,b) ->  vel (sem(a, r), sem(b, r))
      | Not(a) -> non(sem(a, r))
			| LessThan(a,b) -> lessthan(sem(a,r),sem(b,r))
      | Ifthenelse(a,b,c) -> 
            let g = sem(a, r) in
            if typecheck("bool",g) then
               (if g = Bool(true) 
               then sem(b, r)
               else sem(c, r))
            else failwith ("Non e una guardia di tipo bool") 
      | Let(i,e1,e2) -> sem(e2, bind (r ,i, sem(e1, r)))          
      | Fun(i,a) ->  makefun(Fun(i,a), r)
      | Appl(a,b) -> applyfun(sem(a, r), semlist(b, r))
      | Rec(f,e) -> makefunrec (f,e,r)
      | Pipe(t) -> PipeVal(makePipe(t,r))
      | Etup(t) -> EtupVal(evalEtup(t,r))
			| ManyTimes(times,f) -> makeManyTimes(times,f,r)
			| ApplyManyTimes(a,b) -> applymanytimes(sem(a,r),sem(b,r))
			| ApplyPipe(a,b) -> applypipe(sem(a,r),sem(b,r))

	
and applypipe((a:eval), (b:eval)) =
(* a è una PipeVal , b è il parametro attuale che può essere o Bool(_) o Int(_) *)
			if (typecheck ("int",b)) || (typecheck ("bool",b)) then
			(match a with
				| PipeVal([]) -> failwith ("La tupla risulta essere Nil")
				| PipeVal([(e1,env1)]) -> sem(Appl(e1,[toExp(b)]),env1)
				| PipeVal((e1,env1)::rest) -> applypipe( PipeVal( rest ) , sem(Appl( e1,[toExp(b)] ),env1))
				| _ -> failwith ("il primo argomento di applypipe deve essere una PipeVal")
					)
			else failwith ("il secondo argomento di applypipe dev'essere un intero o booleano")
			
			
			
		
and applymanytimes((a:eval), (b: eval)) = if (typecheck ("int",b)) || (typecheck ("bool",b)) then
			(match a with
				| ManyTimesVal(i,e1,r) -> if(i>1) then applymanytimes(ManyTimesVal(i-1,e1,r),sem(Appl(e1,[toExp(b)]),r))
										 else if (i==1) then sem(Appl(e1,[toExp(b)]),r)	
												else failwith ("Non è possibile calcolare la funzione") 
				| _ -> failwith("il primo argomento di applymanytimes deve essere una ManyTimesVal")
			)
			else failwith ("il secondo argomento di applymanytimes dev'essere un intero o booleano")

and toExp (b: eval) = ( match b with
											| Int(c) -> Eint(c)
											| Bool(c) -> Ebool(c)
											| _ -> failwith ("Errore"))																																		



    (* Funzione che trasfroma una tupla in lista di funzioni*)
and makePipe ((t: tuple), (r: eval env)) = (match t with
                              | Nil -> []
                              | Seq(f1,Nil) -> (match (sem (f1,r)) with
                                              | Funval(e1,env1) -> [(e1,env1)]    
                                              | _ -> failwith ("Non una funzione"))
                              | Seq(f1,rest) -> (match (sem (f1,r)) with
                                              | Funval(e1,env1) -> (e1,env1)::makePipe(rest,r)
                                              | _ -> failwith ("Non  una funzione")))

and makeManyTimes((i:int),(e1:exp),(r:eval env)) = (match sem(e1,r) with
																										| Funval(e1,env1) -> ManyTimesVal(i,e1,env1)
																										| _ -> failwith("la chiamata di manytimes non ha una funzione come parametro"))
																										
																										
  (* Funzione che trasforma una tupla in espressioni valutate *)
and evalEtup ((t: tuple),(r: eval env)) = (match t with
                              | Nil->[]
                              | Seq(e1,Nil)-> [sem (e1, r)]
                              | Seq(e1,rest)-> (sem (e1, r))::evalEtup(rest,r))
                              
and semlist(el, r) = match el with
    | [] -> []
    | e::el1 -> sem(e, r) :: (semlist(el1, r))
    
and makefun ((a:exp),(x:eval env)) =
      (match a with
      | Fun(ii,aa) ->
           Funval(a,x)
      | _ -> failwith ("Non e una funzione")) 
    
and applyfun ((ev1:eval),(ev2:eval list)) =
      ( match ev1 with
      | Funval(Fun(ii,aa),r) -> sem(aa, bindlist( r, ii, ev2)) 
      | _ -> failwith ("l'oggetto passato non e un oggetto funzionale"))
      
      
and makefunrec (i, e1, (r:eval env)) = 
    let functional (rr: eval env) = 
       bind(r, i, makefun(e1,rr)) in
       let rec rfix =  function x -> functional rfix x 
                 in makefun(e1, rfix);;


(* vari test durante l'implementazione del codice - Si noti che i test contenuti all'interno di questo blocco sono per il controllo del typecheck o*)
(* dell'effettiva valutazione o esecuzione delle funzioni.*)

let ambiente = emptyenv(Int(0));; (* Dichiarazione dell'ambiente con valore di default *)
let funzione = Fun(["x"],Sum(Den("x"),Eint(2)));; (* funzione(y) = x+2*) 
let funzione2 = Fun(["y"],Prod(Den("y"),Eint(4)));; (* funzione(y) = y*4*)
let funzione3 = Fun(["z"],Diff(Den("z"),Eint(5)));; (* funzione(z) = z-5*)
let manytimes = ManyTimes(3,funzione);; (* Creo la dichiarazione per l'iterazione della funzione "funzione" 3 volte*)
let b = Sum(Eint(2),Eint(3));; (* Crea una espressione di tipo 3+2 *)
let f = sem(ApplyManyTimes(manytimes,b),ambiente);;  (* Risolve la funzione con il passaggio dei parametri con valore calcolato tramite espressione *)
let f = sem(ApplyManyTimes(manytimes,Eint(5)),ambiente);;  (* Risolve la funzione con il passaggio dei parametri con valore diretto *)
let funzione_errata = Fun(["x"],Not(Den("x")));; (* Prova di una funzione che fa il not (verrà applicata ad un argomento intero per testare il typecheck *)
let many_errata = ManyTimes(1,funzione_errata);; (* creazione dell'esecuzione della "funzione_errata" 1 volta *)
let f= sem(ApplyManyTimes(many_errata,b),ambiente);; (* esecuzione di "many_errata" passandogli un parametro errato *)
let pipe = Pipe(Seq(funzione,Seq(funzione2,Seq(funzione3,Nil))));;(* dichiarazione di Pipe *)
let pipeval = sem(pipe,ambiente);; (* trasformo la tupla in una lista di coppie: (funzione,ambiente) *) 
let pipe_risultato = sem(ApplyPipe(pipe,b),ambiente);; (* esecuzione della tupla con passaggio del parametro tramite espressione*)
let pipe_risultato_int = sem(ApplyPipe(pipe,Eint(2)),ambiente);; (* esecuzione della tupla con passaggio del parametro tramite valore diretto*)
let pipe_risultato_errato = sem(ApplyPipe(pipe,Ebool(true)),ambiente);; (* esecuzione della tupla con passaggio del parametro tramite valore diretto ma errato *)
let tupla_vuota = Pipe(Nil);; (* creazione tupla vuota *)
let eval_tupla_vuota = sem(tupla_vuota,ambiente);; (* valutazione della tupla vuota*)
let tupla_vuota_risultato = sem(ApplyPipe(tupla_vuota,b),ambiente);; (* esecuzione della tupla vuota con passaggio del parametro tramite espressione *)
let tupla_for_etup = Seq(pipe,Seq(tupla_vuota,Seq(funzione,Nil)));; (* creazione tupla per etup *)
let creazione_etup = Etup(tupla_for_etup);; (*creazione dell'etup*)
let eval_etup = sem(creazione_etup,ambiente);; (* valutazione dell'etup *)



(* batteria di test per casi particolari *)

(* test di scoping statico *)
let ambiente2 = emptyenv(Int(0));; (* Dichiarazione dell'ambiente con valore di dafault *)
let ambiente_esteso = bind(ambiente2,"y",Int(4));; (* lego y al valore 2 estendendo il vecchio ambiente con quello nuovo*)
let funzione = Fun(["x"],Sum(Den("x"),Den("y")));; (* funzione(x) = x+y*)
let y = sem(Let("y",Eint(3),Den("y")),ambiente_esteso);; (* lego y al valore 3 estendendo il vecchio ambiente con quello nuovo*)
sem(Appl(funzione,[Eint(3)]),ambiente_esteso);; (* controllo scoping statico*) 

(* test dei tipi sulla tupla*)
(* funzioni da int->int*)
let ambiente2 = emptyenv(Int(0));; (* Dichiarazione dell'ambiente con valore di default *)
let funzione = Fun(["x"],Prod(Den("x"),Eint(4)));; (* funzione(y) = y*4*) 
let funzione2 = Fun(["z"],Diff(Den("z"),Eint(5)));; (* funzione(z) = z-5*)
(*funzione bool->bool*)
let funzione3= Fun(["x"],Not(Den("x")));; (* Prova di una funzione che fa il not *)
(*testo la tupla con un errore di tipo*)
let pipe = Pipe(Seq(funzione,Seq(funzione3,Seq(funzione2,Nil))));;
let valutazione_errore = sem(ApplyPipe(pipe,Eint(3)),ambiente2);;
(* testo la tupla senza errori *)
let pipe = Pipe(Seq(funzione,Seq(funzione2,Nil)));;
let valutazione_corretta = sem(ApplyPipe(pipe,Eint(3)),ambiente2);;

(* test di funzioni ricorsive dentro pipe*)
let ambiente = emptyenv(Int(0));; (* Dichiarazione dell'ambiente con valore di default *)
let funzione = Fun(["x"],Prod(Den("x"),Eint(4)));; (* funzione(y) = y*4*)
let fact = Rec("fact", Fun(["x"], Ifthenelse(LessThan(Den "x", Eint 2), Eint 1, Prod(Den "x", Appl (Den "fact", [Diff(Den "x", Eint 1)])))));; (*dichiarazione di funzione ricorsiva*)
let pipe = Pipe(Seq(funzione,Seq(fact,Nil)));; (* dichiarazione di una pipe *)
let pipe_valutata= sem(ApplyPipe(pipe,Eint(1)),ambiente);; (*eseguo la pipe*)


(* test sulle apply per vedere se gli argomenti passati sono conformi alle funzioni create *)
let ambiente = emptyenv(Int(0));; (* Dichiarazione dell'ambiente con valore di default *)
let funzione = Fun(["x"],Sum(Den("x"),Eint(2)));; (* funzione(y) = x+2*) 
let funzione2 = Fun(["y"],Prod(Den("y"),Eint(4)));; (* funzione(y) = y*4*)
let funzione3 = Fun(["z"],Diff(Den("z"),Eint(5)));; (* funzione(z) = z-5*)
let manytimes = ManyTimes(3,funzione);; (* Creo la dichiarazione per l'iterazione della funzione "funzione" 3 volte*)
let pipe = Pipe(Seq(funzione,Seq(funzione2,Seq(funzione3,Nil))));;(* dichiarazione di Pipe *)
sem(ApplyManyTimes(pipe,Eint(2)),ambiente);; (* verifico che dia errore quando non metto come primo argomento di ApplyManyTimes una ManyTimes *)
sem(ApplyPipe(manytimes,Ebool(true)),ambiente);; (* verifico che dia errore quando non metto come primo argomento di una ApplyPipe una Pipe *)
sem(ApplyManyTimes(manytimes,Eint(2)),ambiente);; (* verifico che risolva la manytimes passando i parametri corretti alla ManyTimes *)
sem(ApplyPipe(pipe,Eint(2)),ambiente);; (* verifico che risolva la pipe passando i parametri corretti alla Pipe *)


(* controllo che posso applicare un den alla manyTimes *)
let abc = Let("x",Fun(["x"],Den("x")), ManyTimes(3,funzione));;
sem(abc,ambiente);;
sem(ApplyManyTimes(abc,Eint(2)),ambiente);;