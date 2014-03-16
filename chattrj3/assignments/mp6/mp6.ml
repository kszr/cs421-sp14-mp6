open Mp6common

let rec gather_exp_ty_substitution gamma exp tau =
    let judgment = ExpJudgment(gamma, exp, tau) in
    match exp
    with ConstExp c ->
         let tau' = const_signature c in
         (match unify [(tau, freshInstance tau')]
          with None       -> None
             | Some sigma -> Some(Proof([],judgment), sigma))
    | VarExp x ->
		let value = lookup_env gamma x in
		(match value with
			None -> None
			| Some thing ->	(match unify [(tau, freshInstance thing)] with
				None -> None
				| Some sigma -> Some(Proof([], judgment), sigma)))
	| BinOpAppExp (bo, e1, e2) -> 
						let t1 = fresh() in
						let v1 = gather_exp_ty_substitution gamma e1 t1 in
						let t2 = fresh() in
						let v2 = gather_exp_ty_substitution gamma e2 t2 in
						(match v1 with
							None -> None
							| Some(p1, s1) -> (match v2 with
								None -> None
								| Some(p2, s2) -> let sf = mk_fun_ty t2 tau in
									let sf2 = mk_fun_ty t1 sf in
									let tau' = binop_signature bo in
									let sig_thingo = subst_compose s2 s1 in
									(match unify [(monoTy_lift_subst sig_thingo sf2, freshInstance tau')] with
										None -> None
										| Some thing -> Some(Proof(p1::p2::[], judgment), subst_compose thing sig_thingo) )) )
	| MonOpAppExp (mo, e) ->
				   let newtau = fresh() in
				   let v = gather_exp_ty_substitution gamma e newtau in 
				   (match v with
				   		None -> None
						| Some(p1, s1) ->
							let sigma = mk_fun_ty newtau tau in
				   			let tau' = monop_signature mo in 
				   			(match unify [(monoTy_lift_subst s1 sigma, freshInstance tau')] with
				   				None -> None
				   				| Some pigma -> Some(Proof(p1::[], judgment), subst_compose pigma s1)))
	| IfExp (e1, e2, e3) ->
					let v1 = gather_exp_ty_substitution gamma e1 bool_ty in
					(match v1 with
						None -> None
						| Some (p1, sig1) -> 
							let g2 = env_lift_subst sig1 gamma in
							let v2 = gather_exp_ty_substitution g2 e2 tau in
							(match v2 with
								None -> None
								| Some (p2, sig2) ->
									let sigcomp = subst_compose sig2 sig1 in
									let g3 = env_lift_subst sigcomp gamma in
									let v3 = gather_exp_ty_substitution g3 e3 tau in
									(match v3 with
										None -> None
										| Some (p3, sig3) ->
											let sigcomp3 = subst_compose sig3 sigcomp in
											Some(Proof(p1::p2::p3::[], judgment), sigcomp3)) ))
	| FnExp (x, e) ->
				let tau1 = fresh() in
				let tau2 = fresh() in
				let g1 = ins_env gamma x (polyTy_of_monoTy tau1) in
				let v2 = gather_exp_ty_substitution g1 e tau2 in
				(match v2 with
					None -> None
					| Some (p, sigma) -> 
						let sigfun = monoTy_lift_subst sigma (mk_fun_ty tau1 tau2) in
						let arg1 = monoTy_lift_subst sigma tau in
						(match unify [(arg1, sigfun)] with
							None -> None
							| Some thingo -> Some(Proof(p::[], judgment), subst_compose thingo sigma)     ) )
	| AppExp (e1, e2) -> 
				let tau1 = fresh() in
				let taufn = mk_fun_ty tau1 tau in
				let v1 = gather_exp_ty_substitution gamma e1 taufn in
				(match v1 with 
					None -> None
					| Some (p1, sig1) ->
						let g1 = env_lift_subst sig1 gamma in
						let taufn2 = monoTy_lift_subst sig1 tau1 in
						let v2 = gather_exp_ty_substitution g1 e2 taufn2 in
						(match v2 with
							None -> None
							| Some (p2, sig2) -> Some(Proof(p1::p2::[], judgment), subst_compose sig2 sig1)))
	| RaiseExp e ->
			let v1 = gather_exp_ty_substitution gamma e int_ty in
			(match v1 with 
				None -> None
				| Some (p, sigma) -> Some(Proof(p::[], judgment), sigma))		
	| LetExp (d, e) ->
			let v1 = gather_dec_ty_substitution gamma d in
			(match v1 with
				None -> None
				| Some(p1, delta, sig1) -> 
					let megaenv = sum_env delta (env_lift_subst sig1 gamma) in
					let v2 = gather_exp_ty_substitution megaenv e (monoTy_lift_subst sig1 tau) in
					(match v2 with
						None -> None
						| Some(p2, sig2) ->
							let sigcomp = subst_compose sig2 sig1 in
							Some(Proof(p1::p2::[], judgment), sigcomp) ))
				

and gather_dec_ty_substitution gamma dec = 
	match dec with
		Val (x, e) -> 
			let tau = fresh() in
			let v = gather_exp_ty_substitution gamma e tau in
			(match v with 
				None -> None
				| Some (p, sigma) -> 
					let s1 = monoTy_lift_subst sigma tau in
					let gams = env_lift_subst sigma gamma in
					let envy = make_env x (gen gams s1) in
					let judgment = DecJudgment(gamma, dec, envy) in
					Some(Proof(p::[], judgment), envy, sigma) )
		| Rec (f, x, e) -> 
			let tau2 = fresh() in
			let tau1 = fresh() in
			let g1 = ins_env gamma x (polyTy_of_monoTy tau1) in
			let taufn = mk_fun_ty tau1 tau2 in
			let g2 = ins_env g1 f (polyTy_of_monoTy taufn) in
			let v = gather_exp_ty_substitution g2 e tau2 in
			(match v with
				None -> None
				| Some (p, sigma) ->
					let siggam = env_lift_subst sigma gamma in
					let sigtau = monoTy_lift_subst sigma taufn in
					let envy = make_env f (gen siggam sigtau) in
					let judgment = DecJudgment(gamma, dec, envy) in
					Some(Proof(p::[], judgment), envy, sigma))
		| Seq (dec1, dec2) -> let v = gather_dec_ty_substitution gamma dec1 in
			(match v with 
				None -> None
				| Some(p1, d1, sig1) ->
					let megagamma = sum_env d1 gamma in
					let sigmegagamma = env_lift_subst sig1 megagamma in
					let v2 = gather_dec_ty_substitution sigmegagamma dec2 in
					(match v2 with
						None -> None
						| Some (p2, d2, sig2) ->
							let megadelta = sum_env d2 d1 in
							let sigcomp = subst_compose sig2 sig1 in
							let sigmegadelta = env_lift_subst sigcomp megadelta in
							let judgment = DecJudgment(gamma, dec, sigmegadelta) in
							Some(Proof(p1::p2::[], judgment), sigmegadelta, sigcomp) ))
		| Local (dec1, dec2) -> let v1 = gather_dec_ty_substitution gamma dec1 in 
			(match v1 with
				None -> None
				| Some(p1, delta1, sig1) -> 
					let v2 = gather_dec_ty_substitution (env_lift_subst sig1 (sum_env delta1 gamma)) dec2 in
					(match v2 with
						None -> None
						| Some(p2, delta2, sig2) -> 	
							let sigcomp = subst_compose sig2 sig1 in
							let megadelta = env_lift_subst sigcomp delta2 in
							let judgment = DecJudgment(gamma, dec, delta2) in
							Some(Proof(p1::p2::[], judgment), megadelta, sigcomp)))
