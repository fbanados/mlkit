structure CastConversions =
struct
open LambdaExp

structure CastableTypes =
struct
    val tycon = TyName.mk_TyCon "CastableType"
    val tyname = TyName.freshTyName {tycon = tycon, arity = 0, equality = true}
    val fun_dyn_dyn_tycon = TyName.mk_TyCon "dynFunDynDyn"
    val fun_dyn_dyn_tyname = TyName.freshTyName{tycon = fun_dyn_dyn_tycon, arity=0, equality=true}
    val fun_dyn_dyn_con = Con.mk_con ("dyn_fun_dyn_dyn")
end

structure DynWrapper = struct
    val tyname = TyName.tyName_DYN
    val tycon = TyName.tycon(tyname)
    val wrappercons = { string = Con.mk_con("dyn_string"),
			bool = Con.mk_con("dyn_bool"),
			fun_dyn_dyn = CastableTypes.fun_dyn_dyn_con}
    val wrappertypes : (con * Type option) list =
	(* this tuple associates a constructor with the option Type of its arguments. Since all are atomic for now, we don't need any Type so all are NONE. *)
	[(#string wrappercons, SOME(stringType)),
	 (#bool wrappercons, SOME(boolType)),
	 (#fun_dyn_dyn wrappercons, SOME(ARROWtype([dynType],[dynType])))]
	    
    end
	
(* runtimeDataBinds adds the required datatype constructors to the evaluation environment *)
fun runtime_datatype_binds db =
    (* add data bindings, which work as a list of list of tuples *)
    (* each tuple is tyvar list * TyName * (con * Type option) list. *)
    let val dyn_datatype_bind = ([], TyName.tyName_DYN, DynWrapper.wrappertypes)
    in
	db @ [[dyn_datatype_bind]]
    end
	
	
(* gen_identity : This function generates Identity Cast Functions of type t *)
fun gen_identity (ty : Type) : LambdaExp =
    let val z = Lvars.newLvar()
    in
	FN{pat= [(z, ty)],
	   body = VAR{lvar=z,instances=[]}}
    end

(* gen_failing : This function generates a Failing cast function of source type ty1 and destination type ty2*)
fun gen_failing (ty2 : Type) (ty1 : Type) : LambdaExp =
    let val z = Lvars.newLvar()
    in
	FN{pat = [(z, ty1)],
	   body = RAISE(PRIM(EXCONprim(Excon.ex_CASTERROR),[]),
			Types [ty2])}
    end

(* gen_switch_wrapped : This function generates a function that typecases a dyn, and if so evaluates a LambdaExp, otherwise fails with a CastError. *)
(* use with wan of the wrappercons in DynWrapper *)
fun gen_switch_wrapped (ty1 : Type) (wrapcon : con) : (lvar * (LambdaExp -> LambdaExp))=
    let val z0 = Lvars.new_named_lvar("SwitchWrappedZ0")
    in
	(z0,
	 fn (iftrue : LambdaExp) => 
	    let val dyn_switch = [((wrapcon,NONE),iftrue)] (* (con*lvar option). now is NONE beause dynwrappers are simple *)
	    in
		FN{pat= [(z0 , LambdaExp.dynType)],
		   body = SWITCH_C( SWITCH(VAR{lvar=z0, instances=[]},
					   dyn_switch,
					   (* assuming behaviour is "else do", throw the exception otherwise. *)
					   SOME(RAISE(PRIM(EXCONprim(Excon.ex_CASTERROR),[]),
						      Types [ty1]))))}
	    end) (* or some lambdaexp*)
    end

fun gen_basic_value_wrapper (ty1 : Type) : LambdaExp =
    let val z = Lvars.new_named_lvar("basic_value_wrapper")
    in
	case ty1 of
	    CONStype (tl, name) =>
	    (if TyName.eq(name, TyName.tyName_STRING)
	     then
		 FN{pat=[(z, ty1)],
		    body = PRIM (CONprim{con=(#string DynWrapper.wrappercons),
					 instances=[]},
				 [VAR{lvar=z,instances=[]}])}
	     else if TyName.eq(name, TyName.tyName_BOOL)
	     then
		 FN{pat=[(z, ty1)],
		    body = PRIM (CONprim({con=(#bool DynWrapper.wrappercons),
					  instances=[]}),
				 [VAR{lvar=z, instances=[]}])}
	     else
		 gen_failing LambdaExp.dynType ty1)
	 |  _  => gen_failing LambdaExp.dynType ty1
     end
	
fun cast_function_ty2_string (ty1: Type) : LambdaExp =
    case ty1 of
	CONStype (tl, name) => (if TyName.eq(name, TyName.tyName_STRING)
				then gen_identity LambdaExp.stringType
				else if TyName.eq(name, TyName.tyName_DYN)
				then let val (z, f) = gen_switch_wrapped LambdaExp.stringType
									 (#string DynWrapper.wrappercons)
				     in
					 f(PRIM(DECONprim{con=(#string DynWrapper.wrappercons), instances=[], lv_opt=NONE},
						[VAR{lvar=z, instances=[]}]))
				     end
				else gen_failing LambdaExp.stringType ty1)
      | _ => gen_failing LambdaExp.stringType ty1 
			 
and cast_function_ty2_bool (ty1 : Type) : LambdaExp =
	case ty1 of
	    CONStype (tl, name) => (if TyName.eq(name, TyName.tyName_BOOL)
				    then gen_identity LambdaExp.boolType
				    else if TyName.eq(name, TyName.tyName_DYN)
				    then let val (z, f) = gen_switch_wrapped LambdaExp.boolType
									     (#bool DynWrapper.wrappercons)
					 in
					     f(PRIM(DECONprim{con=(#bool DynWrapper.wrappercons), instances=[], lv_opt=NONE},
						    [VAR{lvar=z, instances=[]}]))
					 end
				    else gen_failing LambdaExp.stringType ty1)
	  | _ => gen_failing LambdaExp.stringType ty1
			     
and cast_function_ty2_dyn (ty1: Type) : LambdaExp =
    case ty1 of
	CONStype (tl, name) => (if TyName.eq(name, TyName.tyName_DYN)
				then gen_identity LambdaExp.dynType
				else gen_basic_value_wrapper ty1)
      | ARROWtype (_, []) => gen_failing dynType ty1 (* no void functions, please *)
      | ARROWtype (dom, rng) =>
	let val z = Lvars.new_named_lvar("CastToDynFromArow")
	in
	    FN{pat=[(z,ty1)],
	       body = PRIM (CONprim{con=(#fun_dyn_dyn DynWrapper.wrappercons),
				    instances=[]},
			    [APP(cast_function(ARROWtype([dynType], [dynType]),ty1),
				 VAR{lvar=z, instances=[]},
				 NONE)])}
	end
      | _ => gen_failing dynType ty1 (* no other ideas *)
		    
		    
and cast_function_ty2_fn (ty21 : Type) (ty22: Type) (ty1: Type) : LambdaExp =
    case ty1 of
	ARROWtype (ty11 :: [], ty12 :: []) =>
	let val f = Lvars.newLvar()
	    val z = Lvars.newLvar()
	in
	    (* (lambda f : t1 . (lambda z : t21. (cast t22 <= t12 (f (cast t11 <= t21 z))))) *)
	    FN{pat =[(f, ty1)],
	       body = FN{pat=[(z,ty21)],
			 body =APP ( cast_function (ty22, ty11),
				     APP(VAR{lvar=f, instances=[]},
					 APP( cast_function (ty11, ty21),
					      VAR{lvar=z, instances=[]},
					      NONE),
					 NONE),
				     NONE)}}
	end
     |  CONStype(_ , name) => if TyName.eq(name, TyName.tyName_DYN)
			      then
				  let val (z, f) = gen_switch_wrapped (ARROWtype([ty21],[ty22]))
								      (#fun_dyn_dyn DynWrapper.wrappercons)
				  in
				      f(APP(cast_function((ARROWtype([ty21],[ty22])),
								    (ARROWtype([dynType], [dynType]))),
						      (PRIM(DECONprim{con=(#fun_dyn_dyn DynWrapper.wrappercons),
								      instances=[],
								      lv_opt=NONE},
							    [VAR{lvar=z, instances=[]}])),
						      NONE))
				  end				  
			      else gen_failing (ARROWtype([ty21], [ty22])) ty1
     | _ => gen_failing  (ARROWtype([ty21], [ty22])) ty1
(* cast_function generates the anonymous function wrappers for casts *)

and cast_function (ty2 : Type, ty1 : Type) : LambdaExp=
    case ty2 of
	    CONStype(_, name) => (if TyName.eq(name, TyName.tyName_DYN)
				  then cast_function_ty2_dyn ty1
				  else if TyName.eq(name, TyName.tyName_STRING)
				  then cast_function_ty2_string ty1
				  else if TyName.eq(name, TyName.tyName_BOOL)
				  then cast_function_ty2_bool ty1
				  else (* for now, nothing to do *)
				      gen_failing ty2 ty1)
	  | ARROWtype( dom :: [] , rng :: [])  =>
	    cast_function_ty2_fn dom rng ty1
	  | _ => (gen_failing ty2 ty1)(* for now, nothing to do *)
			     
(*
     * Cast-removal: This optimization transforms casts into simpler
     * sets of instructions, so that we don't need to modify the region
     * language.
     *)

fun cast_remove (lamb : LambdaExp) =
    let fun replace_casts (lamb : LambdaExp) : LambdaExp =
	    let fun replace_switch ((e1, exps, e2) : (LambdaExp * ('a * LambdaExp) list * LambdaExp option)) : 'a Switch  =
				    let val e2' = case e2 of
						      SOME(e) => SOME(replace_casts e)
						    | NONE => NONE
				    in SWITCH(replace_casts e1,
					      (map (fn ((a, exp) : ('a * LambdaExp)) => (a, replace_casts exp)) exps),
					      e2')
				    end
		in
		case lamb of
		    CAST{ty2,ty1,exp} =>
		    let val function = cast_function(ty2, ty1)
		    in
			APP(function,
			    (replace_casts exp),
			    NONE)
		    end
		  | FN{pat,body}  => FN{pat=pat, body=replace_casts body}
		  | LET{pat, bind, scope} => LET{pat=pat,
						 bind=replace_casts bind,
						 scope=replace_casts scope}
		  | FIX{functions, scope} =>FIX{functions= map
								(fn x => {lvar=(#lvar x),
									  tyvars=(#tyvars x),
									  Type=(#Type x),
									  bind=(replace_casts (#bind x))})
								functions,
						 scope=replace_casts scope} 
		  | APP(f, arg, tail) => APP(replace_casts f,
					     replace_casts arg,
					     tail)
		  | EXCEPTION (excon, t, exp) => EXCEPTION(excon, t, replace_casts exp)
		  | RAISE (exp, t) => RAISE(replace_casts exp, t)
		  | HANDLE (e1, e2) => HANDLE(replace_casts e1, replace_casts e2)
		  | SWITCH_I {switch as SWITCH(e1, exps, e2), precision} =>
			SWITCH_I{switch=replace_switch (e1,exps,e2),
				 precision=precision}
		  | SWITCH_W{switch as SWITCH(e1, exps, e2), precision} =>
		    SWITCH_W{switch=replace_switch (e1,exps,e2),
			     precision=precision}
		  | SWITCH_S (s as SWITCH(e1, exps, e2)) => SWITCH_S(replace_switch(e1,exps,e2))
		  | SWITCH_C (s as SWITCH(e1, exps, e2)) => SWITCH_C(replace_switch(e1,exps,e2))
		  | SWITCH_E (s as SWITCH(e1, exps, e2)) => SWITCH_E(replace_switch(e1,exps,e2))
		  | PRIM (tp, args) => PRIM(tp, map replace_casts args)
		  | _ =>lamb
	    end
	    
	in
	    replace_casts lamb
	end


end
