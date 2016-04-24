(* Librairies *)

open Graphics;;
(*#load "graphics.cma";;*)



(* Constantes et paramètres *)


let pi = 3.1415
and hauteur = 200
and largeur = 300
and decalage = 11;;  (* Nombres de pixels de la barre de chargement *)
let couleur_infini = [|153;255;255|] ;; (* Bleu ciel *)
let couleur_reflexion_max = [|255;255;255|] ;;
let reflexion_max = 10 
and decr_lum puiss dist = puiss/.(1.+.5.*.dist)
and lum_ambiante = 0.1;; (* par défaut, mettre 0.1 *)
let cote_bloc_mine = 16.
and periode_mine = 16
and taille_mine = 1.;;







(* Types *)

type point = float array ;;

type plan = float array ;; (* Equation cartésienne : ax+by+cz+d=0 -> [|a;b;c;d|] *)

type droite = float array ;; (* [|a;b;c ; d;e;f|] : (a;b;c) point "d'origine", (d,e,f) vecteur directeur NORME*)


type couleur =
  Reflexion
|Transparent
|Couleur of int array
;;

type texture = 
  Uni of couleur 
|Damier of float*float*couleur*couleur (* Largeur et hauteur du carreau *)
|Lum of float 
|Minecraft of int*float*(((int array) array) array)
;;
type polygone = 
  Parallelogramme of (point*point*point*texture) (* 3 sommets a,b,c; on a alors le parallelogramme abdc *)
|Triangle         of (point*point*point*texture) (* 3 sommets *)
|Disque           of (plan*point*float*texture) 
|Sphere           of (point*float*texture)       (* centre,rayon *)
|Cylindre_vert    of (point*float*float*texture) (* centre de la base,rayon,hauteur.  NB : Ce cylindre est nécéssairement orienté selon z *);;

type objet =
  Face     of polygone
|Boite     of point*point*point*point*texture (*O,A,B,C; qui forment une base directe *)
|Pyramide  of (point*point*point*point*texture)
(*|Scene of objet list *)
;;
type scene = objet list;;

let first (a,b,c) = a
and second (a,b,c) = b
and third (a,b,c) = c;;(*useless*)


(* Opérateurs de base *)

let concatene [|a;b;c|] [|d;e;f|] = [|a;b;c;d;e;f|]
and prod_vect [|x1;y1;z1|] [|x2;y2;z2|] = 
  [|y1*.z2 -. y2*.z1;
    x2*.z1 -. x1*.z2;
    x1*.y2 -. x2*.y1|]
and add_tab t1 t2 =                             (* t1 + t2 *)
  let res = Array.make (Array.length t1) 0. in
  (
    for i=0 to (Array.length t1 -1) do
      res.(i) <- t1.(i) +. t2.(i)
    done;
    res;
  )
and add_tab_statique t1 t2 =
  for i=0 to (Array.length t1 -1) do
    t1.(i) <- t1.(i) +. t2.(i)
  done
and sub_tab t1 t2 =                             (* t1 - t2 *)
  let res = Array.make (Array.length t1) 0. in
  (
    for i=0 to (Array.length t1 -1) do
      res.(i) <- t1.(i) -. t2.(i)
    done;
    res;
  )
and mul_tab t k = 
  let res = Array.make (Array.length t ) 0. in
  (
    for i=0 to (Array.length t -1) do
      res.(i) <- t.(i) *. k
    done;
    res;
  )
and mul_tab_statique t k =
  for i=0 to (Array.length t -1) do
    t.(i) <- t.(i) *. k
  done;
and add_matrix t1 t2 =
  for i = 0 to (Array.length t1) -1 do
    for j = 0 to (Array.length t1.(0)) -1 do
      t1.(i).(j) <- t1.(i).(j)+.t2.(i).(j) 
          done
  done
and norme t = sqrt (t.(0)*.t.(0) +. t.(1)*.t.(1) +. t.(2)*.t.(2))
and prod_scal a b = a.(0)*.b.(0) +. a.(1)*.b.(1) +. a.(2)*.b.(2)
;;
let prod_mat t1 t2 = (* t1 est un vecteur colonne de dim 3 *)
  let res = Array.make 3 0. in
  (
    for i=0 to 2 do
      res.(i) <- prod_scal t1 (t2.(i))
    done;
    res
  );;
let prod_mat_statique t1 t2 = (* t1 vecteur colonne, t2 carrée de dim 3 *)
  let temp = prod_mat t1 t2 in
  for i=0 to 2 do
    t1.(i) <- temp.(i)
  done;;
let signe a = 
  if a > 0. 
  then 1.
  else if a < 0.
  then -. 1.
  else 0. ;;
				

let pol_2nd_degre a b c = (* ax^2 + bx + c = 0 *)
  let delta = (b*.b) -. 4.*.a*.c in
  if delta >= 0. then
    let rac_delta = sqrt delta in
    ((rac_delta-.b)/.(2.*.a)),(-.(rac_delta+.b)/.(2.*.a))
  else
    failwith "Pas de racine reelle"
;;
 

let calc_droite (p1:point) (p2:point) = (* Orientée de p1 vers p2 *)
  let res = Array.make 6 0. in
  (
    for i=0 to 2 do
      res.(i)   <- p1.(i);
      res.(i+3) <- p2.(i) -. p1.(i)
    done;
    if res.(3)=0. && res.(4)=0. && res.(5)=0. then
      failwith "Vecteur directeur nul, les deux points sont confondus"
    else
      let n = sqrt (res.(3)*.res.(3) +. res.(4)*.res.(4) +. res.(5)*.res.(5)) in
      for i=3 to 5 do
	res.(i) <- res.(i) /. n
      done;
      res:droite
  )
;;

let calc_plan (p1:point) (p2:point) (p3:point) =
  let vn = prod_vect (sub_tab p2 p1) (sub_tab p3 p1) in
  if vn = [|0.;0.;0.|] then
    failwith "Vecteur normal nul, les 3 points sont alignes"
  else
    let res:plan =[|vn.(0);vn.(1);vn.(2);
      -.vn.(0)*.p1.(0) -.vn.(1)*.p1.(1) -.vn.(2)*.p1.(2)|] in
    res
;;

let calc_plan_vue (pdv:point) vn = 
(* calcule un plan de vecteur normal vn (vn a priori non normé), à distance 1 de pdv *)
  let invnorme = 1./.(norme vn) in
  let vnn = mul_tab vn invnorme in
  [|vnn.(0);vnn.(1);vnn.(2);
    -.(
      vnn.(0)*.(pdv.(0)+.vnn.(0))
      +.vnn.(1)*.(pdv.(1)+.vnn.(1))
      +.vnn.(2)*.(pdv.(2)+.vnn.(2))
    )|]
;;

calc_plan_vue [|2.;0.;0.|] [|5.;5.;5.|];;


let intersect_d_p (d:droite) (p:plan) =  (* renvoie le point d'intersection et sa distance algébrique avec le point d'origine de d, pratique pour les projections ^^ *)
  let den = p.(0)*.d.(3) +. p.(1)*.d.(4) +. p.(2)*.d.(5) in
  if den = 0. then
    failwith "Pas d'intersection entre ce plan et cette droite"
  else
    let p = -. (p.(0)*.d.(0) +. p.(1)*.d.(1) +. p.(2)*.d.(2) +. p.(3)) /. den in
    let res = Array.make 3 0. in
    (
      for i=0 to 2 do
	res.(i) <- d.(i) +. p *. d.(i+3)
      done;
      (res:point),p
    )
;;

(*intersect_d_p ([|0.;0.;0.;1.;1.;1.|]:droite) [|1.;1.;1.;-.4.|];;*)

(* intersect_d_poly renvoie (couleur,(point,distance_algébrique)),vecteur_normal  Le vecteur normal est NORME *)
let intersect_d_poly (d:droite) (p:polygone) = 
  let aux d p =
    match p with
    |Parallelogramme (a,b,c,t) ->
      begin
    	let pl = calc_plan a b c in
	let m,p = intersect_d_p d pl in
	if p <= 0. then
	  (Transparent,(m,p)),[|pl.(0);pl.(1);pl.(2)|]
	else
	  (*Méthode de projection*)

	  let u = sub_tab c a
	  and v = sub_tab b a in
	  let n = prod_vect u v
	  and nab = norme v
	  and nac = norme u in
	  let pab = calc_plan a b (add_tab a n)
	  and pac = calc_plan a c (add_tab a n) in
	  let den1 = pab.(0)*.u.(0) +. pab.(1)*.u.(1) +. pab.(2)*.u.(2)
	  and den2 = pac.(0)*.v.(0) +. pac.(1)*.v.(1) +. pac.(2)*.v.(2) in
	  let projb_m = [|
	    (pab.(1)*.(m.(0)*.u.(1) -. m.(1)*.(u.(0))) +. pab.(2)*.(m.(0)*.u.(2) -. m.(2)*.(u.(0))) -. pab.(3)*.u.(0)) /. den1;
	    (pab.(0)*.(m.(1)*.u.(0) -. m.(0)*.(u.(1))) +. pab.(2)*.(m.(1)*.u.(2) -. m.(2)*.(u.(1))) -. pab.(3)*.u.(1)) /. den1;
	    (pab.(0)*.(m.(2)*.u.(0) -. m.(0)*.(u.(2))) +. pab.(1)*.(m.(2)*.u.(1) -. m.(1)*.(u.(2))) -. pab.(3)*.u.(2)) /. den1 
			|]
	  and projc_m = [|
	    (pac.(1)*.(m.(0)*.v.(1) -. m.(1)*.(v.(0))) +. pac.(2)*.(m.(0)*.v.(2) -. m.(2)*.(v.(0))) -. pac.(3)*.v.(0)) /. den2;
	    (pac.(0)*.(m.(1)*.v.(0) -. m.(0)*.(v.(1))) +. pac.(2)*.(m.(1)*.v.(2) -. m.(2)*.(v.(1))) -. pac.(3)*.v.(1)) /. den2;
	    (pac.(0)*.(m.(2)*.v.(0) -. m.(0)*.(v.(2))) +. pac.(1)*.(m.(2)*.v.(1) -. m.(1)*.(v.(2))) -. pac.(3)*.v.(2)) /. den2 
			|]
	  in let bm = (prod_scal v (sub_tab projb_m a)) /. nab
	  and cm = (prod_scal u (sub_tab projc_m a)) /.nac
	       
	     in let bmn = bm /. (nab)
	     and cmn = cm /. (nac) in

		if bmn<=1. && bmn>=0. && cmn<=1. && cmn>=0. then
		  (* Le point est dans le parallélogramme  *)

		  (
		    match t with
		    |Uni co -> (co,(m,p)),[|pl.(0);pl.(1);pl.(2)|]
		    |Lum ent -> (Couleur [|-1;-1;-1|],(m,p)),[|pl.(0);pl.(1);pl.(2)|]
		    |Minecraft (div,taille,tab) -> (Couleur 
		 				      tab.( (int_of_float (floor (bm/.taille))) mod div).((int_of_float (floor (cm/.taille))) mod div)
		 				      ,(m,p)),[|pl.(0);pl.(1);pl.(2)|]
		    |_     -> failwith "Texture non définie (parallélogramme) "
		  )
		else
		  (Transparent,(m,p)),[|pl.(0);pl.(1);pl.(2)|]
      end
    |Triangle (a,b,c,t) ->
      begin
	(*méthode par produit vectoriel*)
	let pl = calc_plan a b c in
	let m,p = intersect_d_p d pl in
	if p <= 0. then
	  (Transparent,(m,p)),[|pl.(0);pl.(1);pl.(2)|]
	else
	  let ma = sub_tab a m
	  and mb = sub_tab b m
	  and mc = sub_tab c m in
	  let pvab = prod_vect ma mb
	  and pvbc = prod_vect mb mc
	  and pvca = prod_vect mc ma in
	  if (prod_scal pvab pvbc)>0. && (prod_scal pvbc pvca)>0.
	  then
	    (
	      match t with
	      |Uni co -> (co,(m,p)),[|pl.(0);pl.(1);pl.(2)|]
	      |Lum ent -> (Couleur [|-1;-1;-1|],(m,p)),[|pl.(0);pl.(1);pl.(2)|]
	      |_     -> failwith "Texture non définie (triangle) "
	    )
	  else
	    (Transparent,(m,p)),[|pl.(0);pl.(1);pl.(2)|]
      end
    |Disque (pl,c,r,t) ->
      begin
	let m,p = intersect_d_p d pl in
	if p <= 0. then
	  (Transparent,(m,p)),[|pl.(0);pl.(1);pl.(2)|]
	else 
	  let d = norme (sub_tab m c) in
	  if d<=r then
	    (
	      match t with
	      |Uni cl -> (cl,(m,p)),[|pl.(0);pl.(1);pl.(2)|]
	      |Lum ent -> (Couleur [|-1;-1;-1|],(m,p)),[|pl.(0);pl.(1);pl.(2)|]
	      |_      -> failwith "Texture non définie (parallélogramme) "
	    )
	  else
	    (Transparent,(m,p)),[|pl.(0);pl.(1);pl.(2)|]
      end
    |Sphere (c,r,texture) -> 
      begin
	let x0 = d.(0) -. c.(0)
	and y0 = d.(1) -. c.(1)
	and z0 = d.(2) -. c.(2) in 
	(* On se ramène au cas où la sphère est centrée en 0*)
	let t1,t2 = pol_2nd_degre 
	  (d.(3)*.d.(3) +. d.(4)*.d.(4) +. d.(5)*.d.(5)) 
	  (2.*.(d.(3)*.x0 +. d.(4)*.y0 +. d.(5)*.z0))
	  (x0*.x0 +. y0*.y0 +. z0*.z0 -. r*.r) in
	let t= 
	  if t1 >= 0. then
	    if t2 >= 0. then
	      min t1 t2
	    else
	      t1
	  else
	    t2
	in
	let m = [|d.(0) +. t*.d.(3); d.(1) +. t*.d.(4); d.(2) +. t*.d.(5)|]
	in
	let vn = sub_tab m c in
	if t < 0. then
	  ((Transparent,(m,t)),vn)
	else
	  match texture with
	  |Uni coul -> ((coul,(m,t)),vn)
	  |Lum ent  -> ((Couleur [|-1;-1;-1|],(m,t)),vn)
	  |_        -> failwith "Texture non definie (sphere)"
      end
    |Cylindre_vert (c,r,h,texture) -> 
      begin
	let xcb = d.(0) -. c.(0)
	and ycb = d.(1) -. c.(1) in 
	let t2,t1 = pol_2nd_degre (* nb: t1 <= t2 *)
	  (d.(3)*.d.(3) +. d.(4)*.d.(4))
	  (2.*. (xcb*.d.(3) +. ycb*.d.(4)))
	  (xcb*.xcb +. ycb*.ycb -. r*.r) in 
	let p,t,vn,valide = 
	  (let p1 = [|d.(0) +. t1*.d.(3); d.(1) +. t1*.d.(4); d.(2) +. t1*.d.(5)|]
	  and p2 = [|d.(0) +. t2*.d.(3); d.(1) +. t2*.d.(4); d.(2) +. t2*.d.(5)|] in
	   if (t1 >= 0.) && (p1.(2)>=c.(2)) && (p1.(2)<=(h+.c.(2))) then 
	     p1,t1,[|t1*.d.(4)+.xcb;t1*.d.(5)+.ycb;0.|],true
	   else  
	     p2,t2,[|t1*.d.(4)+.xcb;t1*.d.(5)+.ycb;0.|],((t2 >= 0.) && (p2.(2)>=c.(2)) && (p2.(2)<=(h+.c.(2))))
	  ) in (* Si jamais aucun des deux points n'est valide, on prend le 2ème *)
	match texture with
	|_ when (not valide) -> ((Transparent,(p,t)),vn)
	|Uni coul -> ((coul,(p,t)),vn)
	|Minecraft (div,taille,tableau) -> 
	  let rayon = [|p.(0)-.c.(0);p.(1)-.c.(1);0.|]
	  and longueur = Array.length tableau in 
	  let rayon_norme = mul_tab rayon (1. /. r) in	
	  let abs = (((int_of_float (r*.(2.*.pi +. (signe (asin (rayon_norme.(1)))) *. (acos ( rayon_norme.(0))) )/.taille)))  mod longueur)
	  and haut = ((int_of_float (floor ((p.(2)-.c.(2))/.taille))) mod longueur) in 
	  ((Couleur tableau.(abs).(haut),(p,t)),[|rayon_norme.(0);rayon_norme.(1);0.|])
	|_        -> failwith "Texture non definie (cylindre_vert)"
      end

  in
  match aux d p with (* on norme le vecteur normal *)
  |a,b -> let n = 1. /. (norme b) in
	  ( a,(mul_tab b n))
  | _ -> failwith "intersect_poly" 
;;



let reflect m p n d =
	let inci = [|-.d.(3);-.d.(4);-.d.(5)|] in
	let ref_temp = sub_tab (mul_tab n (2. *. prod_scal n inci)) inci in
	let ref = mul_tab ref_temp (1. /. (norme ref_temp))
		in [|m.(0);m.(1);m.(2);ref.(0);ref.(1);ref.(2)|]
;;

let calcule_pixel (l: polygone list) (d:droite) ecl_miroirs= 
  let rec aux d l acc num interdit = 
    (* calcule un lancer de rayon "simple" *)
    (*interdit sert à éviter de calculer le miroir sur lequel on vient de se réfléchir *)
    (*aux renvoie : [((couleur,(point,paramètre ie distance algébrique)), vecteur normal),numéro du solide sur lequel a lieu l'intersection], la droite incidente *)
    if (d.(3)=0. && d.(4)=0. && d.(5)=0.) then failwith "aux: droite nulle" else
      match l,interdit with
      |[],_     -> acc,d
      |(t::q),i -> 
	begin 
	  if num = i 
	  then aux d q acc (num+1) i
	  else

	    match 
	      (
		try intersect_d_poly d t with
		|Failure "Pas d'intersection entre ce plan et cette droite" -> 
		  (Transparent,([|-.50.;-.51.;-.52.|],(-.53.))),[|0.;0.;0.|]
		|Failure "Pas de racine reelle" -> 
		  (Transparent,([|-.54.;-.55.;-.56.|],(-.57.))),[|0.;0.;0.|]
	      ),acc
	    with
	    |((Transparent,(m,p)),n),_     -> aux d q acc (num+1) interdit
	    |a,[]                          -> aux d q [a,num] (num+1) interdit
	    |((c1,(m1,p1)),n1),[((c2,(m2,p2)),n2),nbr] -> 
	      ( if p1 < p2  then
		  aux d q [((c1,(m1,p1)),n1),num] (num+1) interdit
		else
		  aux d q acc (num+1) interdit
	      )
	    | _,_ -> failwith "calcule_pixel"
	end	
  in
  let rec aux2 d l acc num interdit maxi =
    (* Ici on traite la récursion introduite par les réflexions *)
    (* maxi correspond au nombre maximal de réflexions autorisé *)
    if maxi = 0 then 
      Couleur couleur_reflexion_max
    else
      match aux d l acc num interdit with
      |[],d                          -> Couleur couleur_infini 
      |[((Reflexion,(m,p)),n),nbr],d -> aux2 (reflect m p n d) l [] 0 nbr (maxi-1)
      |[((Couleur c,(m,p)),n),nbr],d -> if c = [|-1;-1;-1|] then Couleur c else couleur_reelle m c l lum_ambiante lum_ambiante n nbr d
      |_,_                           -> failwith "calcule_pixel_failure_--'"
  and couleur_reelle pt coul lst accplus accminus normal numi droite = 
    (* Cette fonction fait le balayage des sources lumineuses pour un point donné *)
    match lst with
    | [] -> 
      let acc = (if (prod_scal [|droite.(3);droite.(4);droite.(5)|] normal ) >=0.
    	then accplus
    	else accminus) in    
      Couleur [|min 255 (int_of_float ((float_of_int coul.(0))*.acc));
		min 255 (int_of_float ((float_of_int coul.(1))*.acc));
		min 255 (int_of_float ((float_of_int coul.(2))*.acc))|]
    | (Sphere (c,r,(Lum pui)))::q -> 
      let p,m = (if ecl_miroirs
	then lumiere pt normal l c pui accplus accminus 
	else accplus,accminus) in
      let [((_,(mr,pr)),nr),_],_ =(aux (calc_droite pt c) l [] 0 numi) in
      if (norme (sub_tab mr c)) <= (1.0001*.r)
      then 
      	(if (prod_scal normal nr) >= 0.
      	 then couleur_reelle pt coul q (p+.(decr_lum pui pr)) m normal numi droite
	 else couleur_reelle pt coul q p (m+.(decr_lum pui pr)) normal numi droite
	)
      else couleur_reelle pt coul q accplus accminus normal numi droite
    | t::q ->  couleur_reelle pt coul q accplus accminus normal numi droite
    | _ -> failwith "couleur_réelle"

  and lumiere pt normale scene source lum accplus accminus=
    (* Cette fonction balaye la liste des miroirs pour un point et une source de lumière donnés *)
    match scene with
    |[] -> accplus,accminus
    |(Sphere(c,r,(Uni Reflexion)))::q ->
      let cx = sub_tab pt c
      and cs = sub_tab source c in
      let nx = norme cx
      and ns = norme cs in
      let biss = add_tab (mul_tab cx (1./.nx)) (mul_tab cs (1./.ns))in
      let pi = add_tab c (mul_tab biss (r/.(norme biss))) in (* Ceci est le point en lequel le rayon qui part de la source et va au point étudié est réfléchi sur la sphère *)
      teste_point pt normale q source lum accplus accminus pi
    |t::q -> lumiere pt normale q source lum accplus accminus
  and teste_point pt normale scene source lum accplus accminus pi= 
    (* faire un balayage de la scène pour déterminer si le rayon lumineux est interrompu ou non *)
    try 
      let v1= sub_tab source pi
      and v2= sub_tab pt pi in
      let n1= norme v1
      and n2= norme v2 in
      if (prod_scal v1 normale)*.(prod_scal v2 normale)<=0. ||
	(let [((_,(_,p)),_),_],_ = aux (concatene pi (mul_tab v1 (1./.n1))) l [] 0 (-1) in (p*.1.0001)<n1) ||
	(let [((_,(_,p)),_),_],_ = aux (concatene pi (mul_tab v2 (1./.n2))) l [] 0 (-1) in (p*.1.0001)<n2)
      then lumiere pt normale scene source lum accplus accminus
      else 
	if (prod_scal v1 normale)>0.
	then lumiere pt normale scene source lum (accplus+.(decr_lum lum (n1+.n2))) accminus
	else lumiere pt normale scene source lum accplus (accminus+.(decr_lum lum (n1+.n2)))
    with
    |Failure "aux: droite nulle" -> lumiere pt normale scene source lum accplus accminus
  in (aux2 d l [] 0 (-1) reflexion_max)
;;







let calcule_ecran h l (pdv:point) (p:plan) (decor:polygone list) zoom inclinaison (*radians*) barre_progression ecl_miroirs=
  if barre_progression then
    (
      (
	try set_color white with 
	|Graphics.Graphic_failure "graphic screen not opened" 
	  -> (open_graph (" "^(string_of_int l)^"x"^(string_of_int (h+decalage)));
	      auto_synchronize false)
      );
      set_color white;
      fill_rect 0 0 l decalage;
      synchronize ();
      set_color blue;
    );
  let po,d = intersect_d_p [|pdv.(0);pdv.(1);pdv.(2);p.(0);p.(1);p.(2)|] p 
  (* Projeté orthogonal du pdv sur le plan *)
  in

  let genere_base () = (* Génère deux vecteurs orthogonaux normés à 1/zoom et orientés selon la valeur de inclinaison, pour les balayages de l'écran *)
    let e1,e2 = (* Base "inclinaison 0", avec norme = 1/zoom *)
      let sens = (if (prod_scal (sub_tab pdv po) [|p.(0);p.(1);p.(2)|]) > 0.
	then 1. else -.1.) in
      let vn = mul_tab [|p.(0);p.(1);p.(2)|] sens  
      (* Vecteur normal au plan orienté du plan vers le point de vue, non normé *)
      in
      let vectbase1 = prod_vect [|0.;0.;1.|] vn in
      match vectbase1 with
      |[|0.;0.;0.|] -> let n = 1./.zoom in [|n;0.;0.|],[|0.;n;0.|]
      |_            -> 
	let n  = 1./.(norme vn)
	and n1 = 1./.((norme vectbase1)*.zoom*.(float_of_int l)) in
	(mul_tab vectbase1 n1),(mul_tab (prod_vect vn vectbase1) (n*.n1))
    in
    let ci = cos inclinaison
    and si = sin inclinaison in
    (add_tab (mul_tab e1 ci)     (mul_tab e2 si)),
    (add_tab (mul_tab e1 (-.si)) (mul_tab e2 ci))      
  in

  let e1,e2 = genere_base () in
  let coin = sub_tab po (add_tab 
			   (mul_tab e1 (float_of_int (l/2)))
			   (mul_tab e2 (float_of_int (h/2)))) in
  let res = Array.make_matrix h l (Couleur [|255;51;204|]) (*Rose bonbon un peu violet : synonyme d'erreur ^^ *)
  in
  for j = 0 to l-1 do
    for i = 0 to h-1 do
      res.(i).(j) <- 
	  let dr = calc_droite pdv 
	      (add_tab coin (
		add_tab (mul_tab e2 (float_of_int i))
		  (mul_tab e1 (float_of_int j)))
	      )in	 
	  try  calcule_pixel decor dr ecl_miroirs
	  with
	  |Invalid_argument arg -> 
	    print_string "Erreur rattrapée : calcule_pixel :";
	    print_newline ();
	    print_string ("Invalid_argument "^arg);
	    print_newline ();
	    print_string ("x = "^(string_of_int j));
	    print_newline ();
	    print_string ("y = "^(string_of_int i));
	    print_newline ();
	    print_string ("droite = [|"^(string_of_float dr.(0))^";"
	                               ^(string_of_float dr.(1))^";"
				       ^(string_of_float dr.(2))^";"
				       ^(string_of_float dr.(3))^";"
				       ^(string_of_float dr.(4))^";"
	                               ^(string_of_float dr.(5))^"|]");
	    print_newline ();
	    print_newline ();
	    Couleur [|0;0;0|]
    done;
    if barre_progression then
      (
	moveto j 3;
	set_color (rgb 0 60 (134+120*j/l));
	lineto j 6;
	synchronize ();
      )
  done;
  res
;;


let affichage h l pdv p decor zoom inclinaison ecl_miroirs=
  let ecran = calcule_ecran h l pdv p decor zoom inclinaison true ecl_miroirs in
  for i = 0 to h-1 do
    for j = 0 to l-1 do
      (match ecran.(i).(j) with
      |Couleur c -> set_color (rgb c.(0) c.(1) c.(2))
      |_         -> failwith "Affichage de cette couleur impossible"
      );
	plot j (i+decalage)
    done
  done;
  synchronize ()
;;
				

let prepare_scene (s:scene) =
  let rec aux s acc = match s with
    |[]                   -> acc
    |(Face p)::q          -> aux q (p::acc)
    |(Boite (o,a,b,c,t))::q -> 
      (let oa = sub_tab a o
      and ob = sub_tab b o
      and oc = sub_tab c o in
      (* On génère les 4 autres points du cube *)
      let o2 = add_tab o (add_tab oa (add_tab ob oc)) in
      let a2 = sub_tab o2 oa
      and b2 = sub_tab o2 ob
      and c2 = sub_tab o2 oc in 
      let p1,p2,p3,p4,p5,p6 =
	(Parallelogramme (o,a,b,t)),
	(Parallelogramme (o,b,c,t)),
	(Parallelogramme (o,c,a,t)),
	(Parallelogramme (o2,a2,b2,t)),
	(Parallelogramme (o2,b2,c2,t)),
	(Parallelogramme (o2,c2,a2,t))in
      aux q (p1::p2::p3::p4::p5::p6::acc)
      )
   |Pyramide (a,b,c,d,t)::q ->
     (let t1 = Triangle (a,b,c,t)
      and t2 = Triangle (b,c,d,t)
      and t3 = Triangle (c,d,a,t)
      and t4 = Triangle (b,d,a,t) in
     aux q (t1::t2::t3::t4::acc)
     )
  in
aux s []
;;

let minecraft_noise [|r;g;b|] [|coef_r;coef_g;coef_b|] divisions = 
  let couleur = Array.make_matrix divisions divisions [|0;0;0|] in
  for i = 0 to divisions-1 do
    for j = 0 to divisions-1 do
      let bonus = ((Random.int 20) -10) in
      couleur.(i).(j) <-[|min 255 (max 0 (r+bonus*coef_r));min 255 (max 0 (g+bonus*coef_g));min 255 (max 0 (b+bonus*coef_b))|]
			  done
    done;
    couleur;;



(* interpolation de Perlin *)

(*let taille_finale = 1000;;
let pix = 1;;
let persistance = 1. (*gain en amplitude*);;
let reduction = 0.65 (*réduction du pas*);;*)

let randomization tab = 
  for i = 0 to (Array.length tab) -1 do
    for j = 0 to (Array.length tab) -1 do
      tab.(i).(j) <- Random.float 1.
    done
  done;;

let interpolation_cos a b x =
  let kx = (1. -. cos ( x *. pi)) /. 2. in
  ( a *. (1. -. kx) +. b *. kx);;
let inter_cos_carre a b c d x y =  (*carre ABCD*)
  interpolation_cos 
    (interpolation_cos a b x)
    (interpolation_cos d c x)
        y ;;

let perlin_cos amplitude pas base taille_finale =
  let res = Array.make_matrix taille_finale taille_finale 0.
  and division =  taille_finale / pas in
  for i = 0 to division  do
    for j = 0 to division  do
      for k = pas*i to min (pas *(i+1) -1) (taille_finale -1 ) do
	for l = pas*j to min (pas*(j+1) -1) (taille_finale -1 ) do
	  res.(k).(l) <-(amplitude *.
					(inter_cos_carre 
					   base.(i*pas).(j*pas)
					   base.(min ((i+1)*pas ) (taille_finale -1)).(j*pas)
					   base.(min ((i+1)*pas ) (taille_finale -1)).(min ((j+1)*pas ) (taille_finale -1))
					   base.(i*pas).(min ((j+1)*pas ) (taille_finale -1 ))
					   ((float_of_int (k-pas*i)) /. (float_of_int pas))
					   ((float_of_int (l-pas*j)) /. (float_of_int pas))
					))
	    
	done
      done
    done
  done;
  res;;
(*
affichage (perlin_cos 1. 10 base);;
affichage (perlin_cos persistance 5 base);;
affichage (perlin_cos (persistance*.persistance) 2 base);;*)

 

let perlin octave pas base persistance reduction = (*perlin devrait être appelée sur un tableau de flottants de 0 à 1*)
  (* octave : nb d'interpolations successives
     pas : taille du premier decoupage
     base : texture à interpoler (/!\ nécéssairement matrice carrée)
     persistance : gain en amplitude à chaque nouvelle interpolation
     reduction : affinage du pas à chaque nouvelle interpolation
  *)
  let taille_finale = Array.length base in
  let amplitude = ref 1.
  and pas_p = ref pas
  and res = Array.make_matrix taille_finale taille_finale 0. in
  for i = 1 to octave do
    if !pas_p <> 0 then
      (add_matrix res (perlin_cos !amplitude !pas_p base taille_finale);
       amplitude := !amplitude *. persistance;
       pas_p := int_of_float ( (float_of_int !pas_p) *. reduction) )
    else ()
  done;
  if persistance <> 1. 
  then
    for i = 0 to taille_finale -1 do
      for j = 0 to taille_finale -1 do
	res.(i).(j) <-(((res.(i).(j))) /. ((1. -. !amplitude)/.(1. -. persistance))) 
      done
    done
  else
    for i = 0 to taille_finale -1 do
      for j = 0 to taille_finale -1 do
	res.(i).(j) <- (res.(i).(j)) /. (float_of_int octave )
      done
    done;
  res;;

(*affichage (perlin 10 taille_finale base persistance reduction) 1;;*)

let perturbation coul base pertu =
  let t = Array.length coul in
  let res = Array.make_matrix t t 0 in
  for i = 0 to t-1 do
    for j = 0 to t-1 do
      res.(i).(j) <- max(min (coul.(i).(j) + int_of_float (pertu *. (0.5 -. base.(i).(j) ) ) ) 255) 0
    done
  done;
  res;;

let minecraft_noise [|r;g;b|] [|coef_r;coef_g;coef_b|] divisions = 
  let couleur = Array.make_matrix divisions divisions [|0;0;0|] in
  for i = 0 to divisions-1 do
    for j = 0 to divisions-1 do
      let bonus = ((Random.int 20) -10) in
      couleur.(i).(j) <-[|min 255 (max 0 (r+bonus*coef_r));min 255 (max 0 (g+bonus*coef_g));min 255 (max 0 (b+bonus*coef_b))|]
    done
  done;
  couleur;;

let transfo_minecraft tab = 
  let taille_finale = Array.length tab in
  let r,g,b = Array.make_matrix taille_finale taille_finale 0,
    Array.make_matrix taille_finale taille_finale 0,
    Array.make_matrix taille_finale taille_finale 0 in
  for i = 0 to taille_finale -1 do
    for j = 0 to taille_finale -1 do
      r.(i).(j) <- tab.(i).(j).(0);
      g.(i).(j) <- tab.(i).(j).(1);
      b.(i).(j) <- tab.(i).(j).(2)
    done
  done;
  r,g,b
and transfo_minecraft_back r g b = 
  let taille_finale = Array.length r in
  let tab = Array.make taille_finale [|[||]|] in
  for i = 0 to taille_finale -1 do
    tab.(i) <- Array.make_matrix taille_finale 3 0
  done;
  for i = 0 to taille_finale -1 do
    for j = 0 to taille_finale -1 do
      tab.(i).(j).(0) <- r.(i).(j);
      tab.(i).(j).(1) <- g.(i).(j);
      tab.(i).(j).(2) <- b.(i).(j)
    done
  done;
  tab;;

let affichage_rgb tab pix = 
  let taille_finale = Array.length tab in
  Graphics.open_graph (" "^(string_of_int (pix*taille_finale))^"x"^(string_of_int (pix*taille_finale)));
  for i=0 to (Array.length tab) -1 do
    for j=0 to (Array.length tab) -1 do
      Graphics.set_color (Graphics.rgb tab.(i).(j).(0) tab.(i).(j).(1) tab.(i).(j).(2));
      Graphics.fill_rect (pix*i) (pix*j) pix pix
    done
  done;;

(*affichage_rgb 
	(perlin 7 taille_finale base1)
	(perlin 7 taille_finale base2)
	(perlin 7 taille_finale base3);;*)

let perlin_cos_minecraft [|r;g;b|] pertu octave taille_finale pas persistance reduction = 
  let base = Array.make_matrix taille_finale taille_finale 0. in
  randomization base;
  let bruit = (perlin octave pas base persistance reduction) in
  let cr,cg,cb = (Array.make_matrix taille_finale taille_finale r),(Array.make_matrix taille_finale taille_finale g),(Array.make_matrix taille_finale taille_finale b) in
  let resr,resg,resb=(perturbation cr bruit pertu),(perturbation cg bruit pertu),(perturbation cb bruit pertu)
  in transfo_minecraft_back resr resg resb
;;
			
(*affichage_rgb (perlin_cos_minecraft [|51;153;0|]  30. 10 300 300 persistance reduction) 1;;*)
let find_color e s =
  let i = ref 1 
  and t = Array.length s in
  while e<=s.(!i) && !i < t-1 do
    i := !i +1
  done;
  if e <= s.(!i-1) 
  then (!i -1)
  else !i;;


let seuil vals coul octave taille_finale pas persistance reduction = 
  let base = Array.make_matrix taille_finale taille_finale 0. in
  randomization base;
  let bruit = (perlin octave pas base persistance reduction) in
  let res = Array.make_matrix taille_finale taille_finale (Array.make taille_finale 0) in	
  for i = 0 to taille_finale - 1 do
    for j = 0 to taille_finale - 1 do
      let case =  (find_color (bruit.(i).(j)) vals) in
      res.(i).(j) <- coul.(case)
    done
  done;
  res;;

let perlin_colonne colonne pertu octave pas persistance taille_finale reduction coul=
  let base = Array.make_matrix taille_finale taille_finale 0. in
  randomization base;
  let bruit = (perlin octave pas base persistance reduction) in
  let res = Array.make_matrix taille_finale taille_finale (Array.make taille_finale 0) in
  for i = 0 to taille_finale - 1 do
    for j = 0 to taille_finale - 1 do
      let k = (1. -. cos ((float_of_int colonne) *.(2. *. pi *. ((float_of_int (i))/.(float_of_int(taille_finale)) +. pertu *. bruit.(i).(j)))))/.2. in
      res.(i).(j) <- [|int_of_float ( (1. -. k) *. (float_of_int (coul.(0).(0))) +. k *. (float_of_int (coul.(1).(0))));
		       int_of_float ( (1. -. k) *. (float_of_int (coul.(0).(1))) +. k *. (float_of_int (coul.(1).(1))));
		       int_of_float ( (1. -. k) *. (float_of_int (coul.(0).(2))) +. k *. (float_of_int (coul.(1).(2))));
		     |]
    done
  done;
  res;;



(*
let herbe =         Minecraft (1000,taille_mine,(minecraft_noise [|51;153;0|]    [|5;5;5|] 1000))
and terre =         Minecraft (1000,taille_mine,(minecraft_noise [|94;43;0|]     [|5;5;5|] 1000))
and sable =         Minecraft (1000,taille_mine,(minecraft_noise [|240;230;140|] [|5;5;5|] 1000))
and torche_manche = Minecraft (periode_mine,taille_mine,(minecraft_noise [|40;31;20|]    [|5;5;5|] periode_mine))
and torche_feu =    Minecraft (periode_mine,taille_mine,(minecraft_noise [|239;134;0|]   [|5;5;5|] periode_mine))

;;

let periode_perlin = 300 and taille_perlin = 0.1 and fact = 50.;;
let herbe_perlin =         Minecraft (periode_perlin,taille_perlin,(perlin_cos_minecraft [|51;153;0|]  fact 10 periode_perlin periode_perlin 1.5 0.7))
and terre_perlin =         Minecraft (periode_perlin,taille_perlin,(perlin_cos_minecraft [|94;43;0|]  fact 10 periode_perlin periode_perlin 1.5 0.7))
and sable_perlin =         Minecraft (periode_perlin,taille_perlin,(perlin_cos_minecraft [|240;230;140|]  fact 10 periode_perlin periode_perlin 1.5 0.7))
and torche_manche_perlin = Minecraft (periode_perlin,taille_perlin,(perlin_cos_minecraft [|40;31;20|]  fact 10 periode_perlin periode_perlin 1.5 0.7))
and torche_feu_perlin =    Minecraft (periode_perlin,taille_perlin,(perlin_cos_minecraft [|239;134;0|]  fact 10 periode_perlin periode_perlin 1.5 0.7))
;;
let add_bloc bloc [|a;b;c|] decor  = 
  let ptitcube = cote_bloc_mine in
    if bloc= "torche" then
      (let c1 = Boite ([|a;b;c|],[|a+.ptitcube/.8.;b;c|],[|a;b+.ptitcube/.8.;c|],[|a;b;c+.ptitcube*.7./.8.|],(torche_manche))
      and c2 = Boite ([|a;b;c+.ptitcube*.7./.8.|],[|a+.ptitcube/.8.;b;c+.ptitcube*.7./.8.|],[|a;b+.ptitcube/.8.;c+.ptitcube*.7./.8.|],[|a;b;c+.ptitcube|],(torche_feu))
      and s1 = Sphere ([|a;b;c+.ptitcube*.1.2|],0.05,Lum 60.)
       in
       s1::((prepare_scene [c1])@(prepare_scene [c2])@decor)
      )
    else
      let f1,f2,f3,f4,f5,f6 =
	(if bloc = "terre" 
	 then
	    Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b+.ptitcube;c|],(terre)),
	  Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b;c+.ptitcube|],(terre)),
	  Parallelogramme ([|a;b;c|],[|a;b+.ptitcube;c|],[|a;b;c+.ptitcube|],(terre)),
	  Parallelogramme ([|a+.ptitcube;b;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a+.ptitcube;b;c+.ptitcube|],(terre)),
	  Parallelogramme ([|a;b+.ptitcube;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a;b+.ptitcube;c+.ptitcube|],(terre)),
	  Parallelogramme ([|a;b;c+.ptitcube|],[|a+.ptitcube;b;c+.ptitcube|],[|a;b+.ptitcube;c+.ptitcube|],(terre))
	 else if bloc = "herbe" then
	   Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b+.ptitcube;c|],(terre)),
	   Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b;c+.ptitcube|],(terre)),
	   Parallelogramme ([|a;b;c|],[|a;b+.ptitcube;c|],[|a;b;c+.ptitcube|],(terre)),
	   Parallelogramme ([|a+.ptitcube;b;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a+.ptitcube;b;c+.ptitcube|],(terre)),
	   Parallelogramme ([|a;b+.ptitcube;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a;b+.ptitcube;c+.ptitcube|],(terre)),
	   Parallelogramme ([|a;b;c+.ptitcube|],[|a+.ptitcube;b;c+.ptitcube|],[|a;b+.ptitcube;c+.ptitcube|],(herbe)) 
	 else if bloc = "sable" then
	   Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b+.ptitcube;c|],(sable)),
	   Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b;c+.ptitcube|],(sable)),
	   Parallelogramme ([|a;b;c|],[|a;b+.ptitcube;c|],[|a;b;c+.ptitcube|],(sable)),
	   Parallelogramme ([|a+.ptitcube;b;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a+.ptitcube;b;c+.ptitcube|],(sable)),
	   Parallelogramme ([|a;b+.ptitcube;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a;b+.ptitcube;c+.ptitcube|],(sable)),
	   Parallelogramme ([|a;b;c+.ptitcube|],[|a+.ptitcube;b;c+.ptitcube|],[|a;b+.ptitcube;c+.ptitcube|],(sable)) 
	 else
	   Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b+.ptitcube;c|],(Uni (Couleur [|255;0;204|]))),
	   Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b;c+.ptitcube|],(Uni (Couleur [|255;0;204|]))),
	   Parallelogramme ([|a;b;c|],[|a;b+.ptitcube;c|],[|a;b;c+.ptitcube|],(Uni (Couleur [|255;0;204|]))),
	   Parallelogramme ([|a+.ptitcube;b;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a+.ptitcube;b;c+.ptitcube|],(Uni (Couleur [|255;0;204|]))),
	   Parallelogramme ([|a;b+.ptitcube;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a;b+.ptitcube;c+.ptitcube|],(Uni (Couleur [|255;0;204|]))),
	   Parallelogramme ([|a;b;c+.ptitcube|],[|a+.ptitcube;b;c+.ptitcube|],[|a;b+.ptitcube;c+.ptitcube|],(Uni (Couleur [|255;0;204|]))) 
	)
      in f1::f2::f3::f4::f5::f6::decor;;

let add_bloc_perlin bloc [|a;b;c|] decor  = 
  let ptitcube = cote_bloc_mine in
    if bloc= "torche" then
      (let c1 = Boite ([|a;b;c|],[|a+.ptitcube/.8.;b;c|],[|a;b+.ptitcube/.8.;c|],[|a;b;c+.ptitcube*.7./.8.|],(torche_manche_perlin))
      and c2 = Boite ([|a;b;c+.ptitcube*.7./.8.|],[|a+.ptitcube/.8.;b;c+.ptitcube*.7./.8.|],[|a;b+.ptitcube/.8.;c+.ptitcube*.7./.8.|],[|a;b;c+.ptitcube|],(torche_feu_perlin))
      and s1 = Sphere ([|a;b;c+.ptitcube*.1.2|],0.05,Lum 60.)
       in
       s1::((prepare_scene [c1])@(prepare_scene [c2])@decor)
      )
    else
      let f1,f2,f3,f4,f5,f6 =
	(if bloc = "terre" 
	 then
	    Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b+.ptitcube;c|],(terre_perlin)),
	  Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b;c+.ptitcube|],(terre_perlin)),
	  Parallelogramme ([|a;b;c|],[|a;b+.ptitcube;c|],[|a;b;c+.ptitcube|],(terre_perlin)),
	  Parallelogramme ([|a+.ptitcube;b;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a+.ptitcube;b;c+.ptitcube|],(terre_perlin)),
	  Parallelogramme ([|a;b+.ptitcube;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a;b+.ptitcube;c+.ptitcube|],(terre_perlin)),
	  Parallelogramme ([|a;b;c+.ptitcube|],[|a+.ptitcube;b;c+.ptitcube|],[|a;b+.ptitcube;c+.ptitcube|],(terre_perlin))
	 else if bloc = "herbe" then
	   Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b+.ptitcube;c|],(terre_perlin)),
	   Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b;c+.ptitcube|],(terre_perlin)),
	   Parallelogramme ([|a;b;c|],[|a;b+.ptitcube;c|],[|a;b;c+.ptitcube|],(terre_perlin)),
	   Parallelogramme ([|a+.ptitcube;b;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a+.ptitcube;b;c+.ptitcube|],(terre_perlin)),
	   Parallelogramme ([|a;b+.ptitcube;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a;b+.ptitcube;c+.ptitcube|],(terre_perlin)),
	   Parallelogramme ([|a;b;c+.ptitcube|],[|a+.ptitcube;b;c+.ptitcube|],[|a;b+.ptitcube;c+.ptitcube|],(herbe_perlin)) 
	 else if bloc = "sable" then
	   Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b+.ptitcube;c|],(sable_perlin)),
	   Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b;c+.ptitcube|],(sable_perlin)),
	   Parallelogramme ([|a;b;c|],[|a;b+.ptitcube;c|],[|a;b;c+.ptitcube|],(sable_perlin)),
	   Parallelogramme ([|a+.ptitcube;b;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a+.ptitcube;b;c+.ptitcube|],(sable_perlin)),
	   Parallelogramme ([|a;b+.ptitcube;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a;b+.ptitcube;c+.ptitcube|],(sable_perlin)),
	   Parallelogramme ([|a;b;c+.ptitcube|],[|a+.ptitcube;b;c+.ptitcube|],[|a;b+.ptitcube;c+.ptitcube|],(sable_perlin)) 
	 else
	   Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b+.ptitcube;c|],(Uni (Couleur [|255;0;204|]))),
	   Parallelogramme ([|a;b;c|],[|a+.ptitcube;b;c|],[|a;b;c+.ptitcube|],(Uni (Couleur [|255;0;204|]))),
	   Parallelogramme ([|a;b;c|],[|a;b+.ptitcube;c|],[|a;b;c+.ptitcube|],(Uni (Couleur [|255;0;204|]))),
	   Parallelogramme ([|a+.ptitcube;b;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a+.ptitcube;b;c+.ptitcube|],(Uni (Couleur [|255;0;204|]))),
	   Parallelogramme ([|a;b+.ptitcube;c|],[|a+.ptitcube;b+.ptitcube;c|],[|a;b+.ptitcube;c+.ptitcube|],(Uni (Couleur [|255;0;204|]))),
	   Parallelogramme ([|a;b;c+.ptitcube|],[|a+.ptitcube;b;c+.ptitcube|],[|a;b+.ptitcube;c+.ptitcube|],(Uni (Couleur [|255;0;204|]))) 
	)
      in f1::f2::f3::f4::f5::f6::decor;;

*)




(* Interface *)



let ecrire efface largeur str =
  if efface then
    (
      set_color white;
      fill_rect 0 0 largeur decalage;
      moveto 0 0
    );
  set_color black;
  draw_string str;
  synchronize () 
and demande_flottant ()=
  let rec calcule l pas coef acc= match l with
    |[]   -> acc
    |t::q -> calcule q pas (coef*.pas) (acc +. t*.coef)
  and accum ent dec p_ent signe = 
    match int_of_char (read_key ()) with
    |45 -> accum ent dec p_ent (-.signe)             (* - *)
    |i when i>=48 && i<=57 ->                        (* 1-9 *)
      draw_string (string_of_int (i-48));   
      synchronize ();                   
      if p_ent then
	accum ((float_of_int (i-48))::ent) dec p_ent signe
      else
	accum ent ((float_of_int (i-48))::dec) p_ent signe
    |46 -> 
      (if p_ent then (draw_char '.';synchronize ()));
      accum ent dec false signe                 (* . *)
    |44 -> accum ent dec false signe                 (* , *)
    |13 ->                                           (* Entrée *)
      signe *. (calcule ent 10. 1. (calcule dec 0.1 0.1 0.))
    |27 -> 0.                                        (* Echap *)
    |_  -> accum ent dec p_ent signe
  in
  accum [] [] true 1.
and demande_entier ()=
  let rec accum n = 
    match int_of_char (read_key ()) with
    |13 -> n
    |i when i>=48 && i<=57 ->                        (* 1-9 *)
      draw_string (string_of_int (i-48));   
      synchronize ();
      accum (10*n + i-48)
    |_  -> accum n
  in
  accum 0;;
let rec wait () = match int_of_char (read_key ()) with
  |13 -> ()
  |_  -> wait ()
;;

(*let affiche_textures_minecraft pix = 
  (* pix est le nombre de pixels de l'écran par pixel de la texture *)
  (
    Graphics.open_graph (" "^(string_of_int (4*periode_mine*pix)^"x"^(string_of_int (periode_mine*pix))));
    let extraire (Minecraft (_,_,t)) = t in
    let balaye texture x0 y0 l h = 
      for i=0 to l-1 do
	for j=0 to h-1 do
	  let coul=texture.(j).(i) in
	  Graphics.set_color (Graphics.rgb coul.(0) coul.(1) coul.(2));
	  Graphics.fill_rect (x0 + pix*i) (y0 + pix*j) pix pix
	done
      done
    in
    (
      balaye (extraire herbe) 0 0 periode_mine periode_mine;
      balaye (extraire terre) (periode_mine*pix)   0 periode_mine periode_mine;
      balaye (extraire sable) (2*periode_mine*pix) 0 periode_mine periode_mine;
      balaye (extraire torche_manche) (3*periode_mine*pix) 0 (periode_mine/8) (7*periode_mine/8);
      balaye (extraire torche_feu)    (3*periode_mine*pix) (8*periode_mine) (periode_mine/8) (periode_mine/8)
    );
    wait ();
    close_graph ()
  );;*)
(* perlin_colonne colonne pertu octave pas persistance taille_finale reduction coul*)
let affichage_rgb t pix = 
  let taille_finale = Array.length t in
  Graphics.open_graph (" "^(string_of_int (pix*taille_finale))^"x"^(string_of_int (pix*taille_finale)));
  for i=0 to taille_finale -1 do
    for j=0 to taille_finale -1 do
      Graphics.set_color (Graphics.rgb t.(i).(j).(0) t.(i).(j).(1) t.(i).(j).(2));
      Graphics.fill_rect (pix*i) (pix*j) pix pix
    done
  done;;
(*affiche_textures_minecraft 10;;*)




let rec boucle hauteur largeur pdv vectnorm decor zoomi inclinaisoni ecl_miroirs= 
(* /!\ Cette fonction pourrait modifier les valeurs de pdv et vectnorm par effet de bord *)
  try 
(
  affichage hauteur largeur pdv (calc_plan_vue pdv vectnorm) decor zoomi inclinaisoni ecl_miroirs;
  let zoom = ref zoomi
  and inclinaison = ref inclinaisoni 
  and eclairage_via_miroirs = ref ecl_miroirs in
  while 
    (
      ecrire true largeur "Ready";
      match (read_key ()) with
      |'\027' -> false (* Touche échap *)
      |c   -> 
	begin
	  match c with
	  |'\r'  ->    (* Entrée *)
	    affichage hauteur largeur pdv (calc_plan_vue pdv vectnorm) decor !zoom !inclinaison !eclairage_via_miroirs

	  |'t'   ->    (* Translation selon un axe *)
	    begin
	      ecrire true largeur "Translation selon l'axe : ";
	      match (read_key ()) with	    
	      |'x'   ->    (* Deplacement du pdv selon x *)
		draw_string "x : ";
		synchronize ();
		pdv.(0) <- pdv.(0) +. (demande_flottant ())
	      |'y'   ->    (* Deplacement du pdv selon y *)
		draw_string "y : ";
		synchronize ();
		pdv.(1) <- pdv.(1) +. (demande_flottant ())
	      |'z'   ->    (* Deplacement du pdv selon z *)
		draw_string "z : ";
		synchronize ();
		pdv.(2) <- pdv.(2) +. (demande_flottant ())
	      |_     -> ()
	    end
	  |'z'   -> ecrire true largeur "Avancer de : ";
	    add_tab_statique pdv (mul_tab vectnorm (demande_flottant ()))
	  |'s'   -> ecrire true largeur "Reculer de : ";
	    add_tab_statique pdv (mul_tab vectnorm (-.(demande_flottant ())))
	  |'d'   -> ecrire true largeur "Crabe à droite de : ";
	    add_tab_statique pdv (mul_tab (prod_vect vectnorm [|0.;0.;1.|]) (demande_flottant ()))
	  |'q'   -> ecrire true largeur "Crabe à gauche de : ";
	    add_tab_statique pdv (mul_tab (prod_vect vectnorm [|0.;0.;1.|]) (-.(demande_flottant ())))
	  |'r'   -> (* Tourner la direction du regard *)
	    begin
	      ecrire true largeur "Tourner vers ";
	      match (read_key ()) with	    
	      |'d'   ->    (* Tourner la direction vers la droite *)
		draw_string "la droite (degres) : ";
		synchronize ();
		let angle = -.0.0174532*.(demande_flottant ()) in
		let rot = [|[|cos angle;-.(sin angle);0.|];
			    [|sin angle; cos angle;0.|];
			    [|0.       ; 0.       ;1.|]|] in
		prod_mat_statique vectnorm rot
	      |'q'   ->    (* Tourner la direction vers la gauche *)
		draw_string "la gauche (degres) : ";
		synchronize ();
		let angle = 0.0174532*.(demande_flottant ()) in
		let rot = [|[|cos angle;-.(sin angle);0.|];
			    [|sin angle; cos angle;0.|];
			    [|0.       ; 0.       ;1.|]|] in
		prod_mat_statique vectnorm rot
	      |'z'   ->    (* Tourner la direction vers le bas *)
		draw_string "le bas (degres) : ";
		synchronize ();
		let angle = -.0.0174532*.(demande_flottant ()) in
		let rot = [|[|cos angle;cos angle;-.(sin angle)|];
			    [|cos angle;cos angle;-.(sin angle)|];
			    [|sin angle;sin angle;cos angle|]|] in
		prod_mat_statique vectnorm rot
	      |'s'   ->    (* Tourner la direction vers le haut *)
		draw_string "le haut (degres) : ";
		synchronize ();
		let angle = 0.0174532*.(demande_flottant ()) in
		let rot = [|[|cos angle;cos angle;-.(sin angle)|];
			    [|cos angle;cos angle;-.(sin angle)|];
			    [|sin angle;sin angle;cos angle|]|] in
		prod_mat_statique vectnorm rot
	      |_     -> ()
	    end
	  |'y'  -> 
	    ecrire true largeur "Zoom x : ";
	    let fact = demande_flottant () in
	    if fact > 0. then
	      zoom := !zoom *. fact
	  |'l'  -> 
	    eclairage_via_miroirs := not !eclairage_via_miroirs;
	    ecrire true largeur ("Eclairage via miroirs : " ^ (
	      if !eclairage_via_miroirs then "Active" else "Desactive"));
	    let _=read_key () in ()
	  |'m'  -> 
	    ecrire true largeur "Nouvelle hauteur : ";
	    let h = demande_entier () in
	    (
	      ecrire true largeur "Nouvelle largeur : ";
	      let l = demande_entier () in
	      (
		close_graph ();
		boucle h l pdv vectnorm decor !zoom !inclinaison !eclairage_via_miroirs;
		failwith "boucle : changement de coordonnées"
		  (* /!\ Cette manière de coder est moche, on empile l'environnement à chaque changement. Mais bon il est pas gros et on le fait jamais *)
	      )
	    )

	  |_ -> ()
	end;
	true
    )do
    ()
  done;
  close_graph ()
) with
  |Failure "boucle : changement de coordonnées" -> ()
;;









(* /ban examples *)

(*Exemple 1*)
(*
let pdv = (*[|150.;150.;175.|]*)
 (* [|150.;-150.;175.|]*) [|-25.;-.20.;60.|]
and vectnorm = [|1.;1.;-1.|];;
let plan = calc_plan_vue pdv vectnorm
and zoom = 0.4
and inclinaison = 0.
and hauteur = 200
and largeur = 300
and c_cube = 125.;;




let decor =
[Parallelogramme ([|c_cube;-.c_cube;0.|],[|c_cube;c_cube;0.|],[|-.c_cube;-.c_cube;0.|],(Uni(Couleur [|255;51;0|]))) ; (*sol*)
Parallelogramme ([|c_cube;-.c_cube;2.*.c_cube|],[|c_cube;c_cube;2.*.c_cube|],[|-.c_cube;-.c_cube;2.*.c_cube|],(Uni (Couleur [|153;0;153|]))) ; (*plafond*)
Parallelogramme ([|c_cube;-.c_cube;0.|],[|c_cube;c_cube;0.|],[|c_cube;-.c_cube;2.*.c_cube|],(Uni (Couleur [|255;0;0|]))) ; (*face +x*)
Parallelogramme ([|-.c_cube;-.c_cube;0.|],[|-.c_cube;c_cube;0.|],[|-.c_cube;-.c_cube;2.*.c_cube|],(Uni (Couleur [|0;255;0|]))) ; (*face -x*)
Parallelogramme ([|c_cube;c_cube;0.|],[|-.c_cube;c_cube;0.|],[|c_cube;c_cube;2.*.c_cube|],(Uni (Couleur [|255;0;102|]))) ; (*face +y*)
Parallelogramme ([|c_cube;-.c_cube;0.|],[|-.c_cube;-.c_cube;0.|],[|c_cube;-.c_cube;2.*.c_cube|],(Uni (Couleur [|0;0;255|]))) ; (*face -y*)

Parallelogramme ([|0.;-.10.;0.|],[|0.;-.5.;0.|],[|0.;-.10.;20.|],(Uni (Couleur [|255;0;0|]))) ; (*jambe droite*)
Parallelogramme ([|0.;10.;0.|],[|0.;5.;0.|],[|0.;10.;20.|],(Uni (Couleur [|255;255;0|]))) ; (*jambe gauche*)
Parallelogramme ([|0.;-.10.;20.|],[|0.;10.;20.|],[|0.;-.10.;40.|],(Uni (Couleur [|0;204;0|]))) ; (*buste*)
Parallelogramme ([|0.;-.3.;40.|],[|0.;3.;40.|],[|0.;-.3.;46.|],(Uni (Couleur [|0;0;0|]))) ; (*tete*)
Parallelogramme ( [|0.;-.10.;40.|],[|0.;-.10.;35.|],[|16.;-.10.;40.|],(Uni (Couleur [|255;255;255|]))) ; (*bras droit*)
Parallelogramme ([|0.;10.;40.|],[|0.;10.;35.|],[|16.;10.;40.|],(Uni (Couleur [|102;0;255|])));  (*bras gauche*) 
(*
Parallelogramme ([|15.;5.;15.|],[|25.;-.5.;15.|],[|15.;-.5.;15.|],(Uni (Couleur red)) ); 
	   
Parallelogramme ([|25.;-.5.;25.|],[|25.;5.;25.|],[|15.;-.5.;25.|],(Uni (Couleur blue)) );
	 
Parallelogramme ([|25.;-.5.;15.|],[|25.;5.;15.|],[|25.;-.5.;25.|],(Uni (Couleur green)) );
	  
 Parallelogramme ([|15.;5.;25.|],[|15.;-.5.;25.|],[|15.;5.;15.|],(Uni (Couleur yellow)) );
 Parallelogramme ([|25.;5.;15.|],[|15.;5.;15.|],[|25.;5.;25.|],(Uni (Couleur black)) );
	   
Parallelogramme ([|15.;-.5.;25.|],[|25.;-.5.;25.|],[|15.;-.5.;15.|],(Uni (Couleur white)) );*)
Sphere ([|65.;-.3.;40.|],45.,(Uni Reflexion));
Sphere ([|15.;-15.;15.|],0.1,(Lum 100.))(*;
Sphere ([|15.;15.;15.|],0.1,(Lum 70.));
Sphere ([|-.15.;0.;15.|],0.1,(Lum 20.)) ;
Sphere ([|-.40.;40.;20.|],0.1,(Lum 20.))*)
] ;;
boucle hauteur largeur pdv vectnorm decor zoom inclinaison true;;
*)




(*boucle hauteur largeur pdv vectnorm (add_bloc "herbe" [|-.40.;40.;0.|] decor ) zoom inclinaison false;;*)

();; 
(*
let pdv =  [|0.;0.;50.|]
and vectnorm = [|0.;2.;-1.|];;
let plan = calc_plan_vue pdv vectnorm
and zoom = 0.4
and inclinaison = 0.
and hauteur = 200
and largeur = 300
and c_cube = 125.;;
*)


(*let scene_minecraft = 
  add_bloc "torche" [|0.;20.;0.|]
    ((Sphere ([|-.15.;60.;30.|],10.,(Uni Reflexion)))::
	(Sphere ([|15.;60.;30.|],10.,(Uni Reflexion)))::
	(add_bloc "herbe" [|-.40.;40.;0.|]
	   (add_bloc "torche" [|-.32.;48.;16.|]
	      (add_bloc "sable" [|-.10.;40.;0.|]
		 (add_bloc "torche" [|-.2.;48.;16.|]
		    (add_bloc "terre" [|20.;40.;0.|]
		       (add_bloc "torche" [|28.;48.;16.|] 
			  [Parallelogramme ([|2.*.c_cube;-.2.*.c_cube;0.|],[|2.*.c_cube;2.*.c_cube;0.|],[|-.2.*.c_cube;-.2.*.c_cube;0.|],(herbe)) ]
		       )
		    )
		 )
	      )
	   )
	)
    );;*)

(*boucle hauteur largeur pdv vectnorm scene_minecraft zoom inclinaison false;;*)
(*
let scene_perlin = 
  add_bloc_perlin "torche" [|0.;20.;0.|]
    ((Sphere ([|-.15.;60.;30.|],10.,(Uni Reflexion)))::
	(Sphere ([|15.;60.;30.|],10.,(Uni Reflexion)))::
	(add_bloc_perlin "herbe" [|-.40.;40.;0.|]
	   (add_bloc_perlin "torche" [|-.32.;48.;16.|]
	      (add_bloc_perlin "sable" [|-.10.;40.;0.|]
		 (add_bloc_perlin "torche" [|-.2.;48.;16.|]
		    (add_bloc_perlin "terre" [|20.;40.;0.|]
		       (add_bloc_perlin "torche" [|28.;48.;16.|] 
			  [Parallelogramme ([|2.*.c_cube;-.2.*.c_cube;0.|],[|2.*.c_cube;2.*.c_cube;0.|],[|-.2.*.c_cube;-.2.*.c_cube;0.|],(herbe)) ]
		       )
		    )
		 )
	      )
	   )
	)
    );;
    *)
    
(*perlin_cos_minecraft [|r;g;b|] pertu octave taille_finale pas persistance reduction *)
(*perlin_colonne colonne pertu octave pas persistance taille_finale reduction coul*)
 
(*let taille_perlin = 0.1 and fact = 50.;; (* textures *)

let sable =           Minecraft (2000,taille_perlin,(perlin_cos_minecraft [|192;184;112|]  fact 25 2000 2000 1.9 0.7))
and herbe=            Minecraft (1000,taille_perlin,(perlin_cos_minecraft [|46;153;0|]  fact 20 1000 1000 1.5 0.7))
and torche_feu=       Minecraft (20,taille_perlin,(perlin_cos_minecraft [|239;140;0|]  fact 10 20 20 1.5 0.7))
and marbre_blanc =    Minecraft (100,taille_perlin,(perlin_colonne 30 0.8 12 100 0.75 100 0.7  [|[|200;200;200|]; [|245;245;245|] |]))
and marbre_noir =     Minecraft (100,taille_perlin,(perlin_colonne 30 0.8 12 100 0.75 100 0.7  [|[|16;16;16|]; [|40;40;40|] |]))
and marbre_colonneb = Minecraft (120,taille_perlin,(perlin_colonne 30 0. 12 120 0.9 120 0.7  [|[|140;140;140|]; [|245;245;245|] |]))
and marbre_colonnen = Minecraft (300,taille_perlin,(perlin_colonne 30 0. 12 300 0.9 300 0.7   [|[|16;16;16|]; [|40;40;40|] |]))
and bois =            Minecraft (500,taille_perlin,(perlin_colonne 30 0.2 12 500 1. 500 0.7  [|[|40;15;0|]; [|19;0;0|] |]))
and roche1 =          Minecraft (1000,taille_perlin,(perlin_cos_minecraft [|32;32;32|]  fact 10 1000 1000 1. 0.7))
and roche2 =          Minecraft (1000,taille_perlin,(perlin_cos_minecraft [|100;100;100|]  fact 10 1000 1000 1. 0.7))
and briques =  (  
  let temp =  perlin_cos_minecraft [|175;112;50|]  (3.*.fact) 15 2000 2000 1. 0.7 in
  for j = 0 to 20 do
    let ligne = if j<20 then j*100 else j*100 - 5 in
    for j1 = 0 to 4 do
      for i=0 to 1999 do
	temp.(i).(ligne + j1) <- [|0;0;0|]
      done
    done;
    if j<20
    then
      let c = ref 0 in
      while (!c*200 + 100*(j mod 2)) < 2000 do
	for i = 0 to 4 do
	  for j1 = 0 to 99 do
	    temp.((!c*200 + 100*(j mod 2)) + i).(ligne + j1) <- [|0;0;0|]
	  done
	done;
	c:= !c+1
      done
    else ();
  done;
  Minecraft (2000,taille_perlin,(temp))
)
;;*)
let extraire t = match t with
| Minecraft (_,_,tex) -> tex;;
(*
affichage_rgb (extraire briques) 1;;

let pdv =  [|-.99.;-.99.;100.|]
and vectnorm = [|144.;144.;-.80.|];;
let plan = calc_plan_vue pdv vectnorm
and zoom = 0.4
and inclinaison = 0.
and hauteur = 600
and largeur = 900
;;

let scene_finale = 
( (*escalier*)
prepare_scene 
[Boite ([|44.5;-.45.;0.|],[|99.5;-.45.;0.|],[|44.5;45.;0.|],[|44.5;-.45.;10.|],roche1);
Boite ([|64.5;-.35.;10.|],[|99.5;-.35.;10.|],[|64.5;35.;10.|],[|64.5;-.35.;20.|],roche2);
Boite ([|69.5;-.27.5;20.|],[|99.5;-.27.5;20.|],[|69.5;27.5;20.|],[|69.5;-.27.5;30.|],roche1);
Boite ([|79.5;-.22.5;30.|],[|99.5;-.22.5;30.|],[|79.5;22.5;30.|],[|79.5;-.22.5;40.|],roche2);
(*porte*)
Boite ([|99.;-.20.;40.|],[|100.;-.20.;40.|],[|99.;20.;40.|],[|99.;-.20.;100.|],bois);
Face (Sphere ([|100.;0.;70.|],3., Uni (Couleur [|255;215;0|])))(*;
Face (Sphere ([|100.;10.;80.|],3.,Lum 30.));
Face (Sphere ([|100.;-.10.;80.|],3., Lum 30.))*)]

)
@ 
[ (*sol*)
Parallelogramme ( [|-.99.5;-.99.5;-.0.25|],[|99.5;-.99.5;-.0.25|],[|-.99.5;99.5;-.0.25|],sable);
Parallelogramme ( [|-.44.5;-.44.5;-.0.1|],[|44.5;-.44.5;-.0.1|],[|-.44.5;44.5;-.0.1|], herbe);
(*murs*)
Parallelogramme ( [|-.99.5;-.99.5;-.0.5|],[|99.5;-.99.5;-.0.5|],[|-.99.5;-.99.5;500.|],briques);
Parallelogramme ( [|-.99.5;-.99.5;-.0.5|],[|-.99.5;99.5;-.0.5|],[|-.99.5;-.99.5;500.|],briques);
Parallelogramme ( [|-.99.5;99.5;-.0.5|],[|99.5;99.5;-.0.5|],[|-.99.5;99.5;500.|],briques);
Parallelogramme ( [|99.5;-.99.5;-.0.5|],[|99.5;100.;-.0.5|],[|99.5;-.99.5;500.|],briques);
(*damier...*)
(*L1*)
Parallelogramme ( [|-.25.;15.;0.|],[|-.15.;15.;0.|],[|-.25.;25.;0.|],marbre_noir);
Parallelogramme ( [|-.15.;15.;0.|],[|-.5.;15.;0.|],[|-.15.;25.;0.|],marbre_blanc);
Parallelogramme ( [|-.5.;15.;0.|],[|5.;15.;0.|],[|-.5.;25.;0.|],marbre_noir);
Parallelogramme ( [|5.;15.;0.|],[|15.;15.;0.|],[|5.;25.;0.|],marbre_blanc);
Parallelogramme ( [|15.;15.;0.|],[|25.;15.;0.|],[|15.;25.;0.|],marbre_noir);
(*L2*)
Parallelogramme ( [|-.25.;5.;0.|],[|-.15.;5.;0.|],[|-.25.;15.;0.|],marbre_blanc);
Parallelogramme ( [|-.15.;5.;0.|],[|-.5.;5.;0.|],[|-.15.;15.;0.|],marbre_noir);
Parallelogramme ( [|-.5.;5.;0.|],[|5.;5.;0.|],[|-.5.;15.;0.|],marbre_blanc);
Parallelogramme ( [|5.;5.;0.|],[|15.;5.;0.|],[|5.;15.;0.|],marbre_noir);
Parallelogramme ( [|15.;5.;0.|],[|25.;5.;0.|],[|15.;15.;0.|],marbre_blanc);
(*L3*)
Parallelogramme ( [|-.25.;-.5.;0.|],[|-.15.;-.5.;0.|],[|-.25.;5.;0.|],marbre_noir);
Parallelogramme ( [|-.15.;-.5.;0.|],[|-.5.;-.5.;0.|],[|-.15.;5.;0.|],marbre_blanc);
Parallelogramme ( [|-.5.;-.5.;0.|],[|5.;-.5.;0.|],[|-.5.;5.;0.|],marbre_noir);
Parallelogramme ( [|5.;-.5.;0.|],[|15.;-.5.;0.|],[|5.;5.;0.|],marbre_blanc);
Parallelogramme ( [|15.;-.5.;0.|],[|25.;-.5.;0.|],[|15.;5.;0.|],marbre_noir);
(*L4*)
Parallelogramme ( [|-.25.;-.15.;0.|],[|-.15.;-.15.;0.|],[|-.25.;-.5.;0.|],marbre_blanc);
Parallelogramme ( [|-.15.;-.15.;0.|],[|-.5.;-.15.;0.|],[|-.15.;-.5.;0.|],marbre_noir);
Parallelogramme ( [|-.5.;-.15.;0.|],[|5.;-.15.;0.|],[|-.5.;-.5.;0.|],marbre_blanc);
Parallelogramme ( [|5.;-.15.;0.|],[|15.;-.15.;0.|],[|5.;-.5.;0.|],marbre_noir);
Parallelogramme ( [|15.;-.15.;0.|],[|25.;-.15.;0.|],[|15.;-.5.;0.|],marbre_blanc);
(*L5*)
Parallelogramme ( [|-.25.;-.25.;0.|],[|-.15.;-.25.;0.|],[|-.25.;-.15.;0.|],marbre_noir);
Parallelogramme ( [|-.15.;-.25.;0.|],[|-.5.;-.25.;0.|],[|-.15.;-.15.;0.|],marbre_blanc);
Parallelogramme ( [|-.5.;-.25.;0.|],[|5.;-.25.;0.|],[|-.5.;-.15.;0.|],marbre_noir);
Parallelogramme ( [|5.;-.25.;0.|],[|15.;-.25.;0.|],[|5.;-.15.;0.|],marbre_blanc);
Parallelogramme ( [|15.;-.25.;0.|],[|25.;-.25.;0.|],[|15.;-.15.;0.|],marbre_noir);
(*Sphere ([|16.5;44.5;35.|],3., Lum 60.);*)

(*miroirs*)

Cylindre_vert ([|-82.;0.;0.|],7.5,25.,marbre_colonnen);
Sphere ([|-82.;0.;40.|],20., Uni ( Reflexion));

Cylindre_vert ([|0.;82.;0.|],7.5,25.,marbre_colonnen);
Sphere ([|0.;82.;40.|],20., Uni ( Reflexion));

Cylindre_vert ([|0.;-82.;0.|],7.5,25.,marbre_colonnen);
Sphere ([|0.;-82.;40.|],20., Uni ( Reflexion));

(* luminaires *)

Cylindre_vert ([|16.5;44.5;0.|],5.,20.,marbre_colonneb );
Disque ([|0.;0.;1.;-.20.|],[|16.5;44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|16.5;44.5;35.|],3., Lum 60.);

Cylindre_vert ([|-.16.5;44.5;0.|],5.,20.,marbre_colonneb);
Disque ([|0.;0.;1.;-.20.|],[|-.16.5;44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.16.5;44.5;35.|],3., Lum 60.);


Cylindre_vert ([|16.5;-.44.5;0.|],5.,20.,marbre_colonneb);
Disque ([|0.;0.;1.;-.20.|],[|16.5;-.44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|16.5;-.44.5;35.|],3., Lum 60.);

Cylindre_vert ([|-.16.5;-.44.5;0.|],5.,20.,marbre_colonneb);
Disque ([|0.;0.;1.;-.20.|],[|-.16.5;-.44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.16.5;-.44.5;35.|],3., Lum 60.);


Cylindre_vert ([|-.44.5;16.5;0.|],5.,20.,marbre_colonneb);
Disque ([|0.;0.;1.;-.20.|],[|-.44.5;16.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.44.5;16.5;35.|],3., Lum 60.);

Cylindre_vert ([|-.44.5;-.16.5;0.|],5.,20.,marbre_colonneb);
Disque ([|0.;0.;1.;-.20.|],[|-.44.5;-.16.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.44.5;-.16.5;35.|],3., Lum 60.)
];;

boucle hauteur largeur pdv vectnorm scene_finale zoom inclinaison false;;
();;*)

(* Fin des exemples de développement *)







(* Rendus finaux *)

let pdv =  [|-.95.;-.95.;100.|]
and vectnorm = [|144.;144.;-.80.|];;
let plan = calc_plan_vue pdv vectnorm
and zoom = 0.4
and inclinaison = 0.
and hauteur = 800
and largeur = 1200
;;

(*Rendu 1*)
(*Mettre la luminosité ambiante aux alentours de 1.2*)

(*let scene_finale = 
( (*escalier*)
prepare_scene 
[Boite ([|44.5;-.45.;0.|],[|99.5;-.45.;0.|],[|44.5;45.;0.|],[|44.5;-.45.;10.|],Uni(Couleur [|72;72;72|]));
Boite ([|56.1;-.35.;10.|],[|99.5;-.35.;10.|],[|56.1;35.;10.|],[|56.1;-.35.;20.|],Uni (Couleur [|72;72;72|]));
Boite ([|67.9;-.27.5;20.|],[|99.5;-.27.5;20.|],[|67.9;27.5;20.|],[|67.9;-.27.5;30.|],Uni(Couleur [|72;72;72|]));
Boite ([|79.5;-.22.5;30.|],[|99.5;-.22.5;30.|],[|79.5;22.5;30.|],[|79.5;-.22.5;40.|],Uni (Couleur [|72;72;72|]));
Face (Parallelogramme ([|44.5;-.45.;10.01|],[|99.5;-.45.;10.01|],[|44.5;45.;10.01|],Uni(Couleur [|32;32;32|])));
Face (Parallelogramme ([|56.1;-.35.;20.01|],[|99.5;-.35.;20.01|],[|56.1;35.;20.01|],Uni(Couleur [|32;32;32|])));
Face (Parallelogramme ([|67.9;-.27.5;30.01|],[|99.5;-.27.5;30.01|],[|67.9;27.5;30.01|],Uni(Couleur [|32;32;32|])));
Face (Parallelogramme ([|79.5;-.22.5;40.01|],[|99.5;-.22.5;40.01|],[|79.5;22.5;40.01|],Uni(Couleur [|32;32;32|])));

(*porte*)
Boite ([|99.;-.20.;40.|],[|100.;-.20.;40.|],[|99.;20.;40.|],[|99.;-.20.;100.|],Uni(Couleur [|40;15;0|]));
Face (Sphere ([|100.;0.;70.|],3., Uni (Couleur [|255;215;0|])));
Face (Sphere ([|100.;10.;80.|],3.,Uni (Couleur [|255;255;255|])));
Face (Sphere ([|100.;-.10.;80.|],3.,Uni (Couleur [|255;255;255|])))]

)
@ 
[ (*sol*)
Parallelogramme ( [|-.99.5;-.99.5;-.0.25|],[|99.5;-.99.5;-.0.25|],[|-.99.5;99.5;-.0.25|],Uni(Couleur [|192;184;112|]));
Parallelogramme ( [|-.44.5;-.44.5;-.0.1|],[|44.5;-.44.5;-.0.1|],[|-.44.5;44.5;-.0.1|], Uni(Couleur [|46;153;0|]));
(*murs*)
Parallelogramme ( [|-.99.5;-.99.5;-.0.5|],[|99.5;-.99.5;-.0.5|],[|-.99.5;-.99.5;500.|],Uni(Couleur [|175;112;50|]));
Parallelogramme ( [|-.99.5;-.99.5;-.0.5|],[|-.99.5;99.5;-.0.5|],[|-.99.5;-.99.5;500.|],Uni(Couleur [|165;102;40|]));
Parallelogramme ( [|-.99.5;99.5;-.0.5|],[|99.5;99.5;-.0.5|],[|-.99.5;99.5;500.|],Uni(Couleur [|175;112;50|]));
Parallelogramme ( [|99.5;-.99.5;-.0.5|],[|99.5;100.;-.0.5|],[|99.5;-.99.5;500.|],Uni(Couleur [|165;102;40|]));
(*damier...*)
(*L1*)
Parallelogramme ( [|-.25.;15.;0.|],[|-.15.;15.;0.|],[|-.25.;25.;0.|],Uni(Couleur [|0;0;0|]));
Parallelogramme ( [|-.15.;15.;0.|],[|-.5.;15.;0.|],[|-.15.;25.;0.|],Uni (Couleur [|254;254;254|]));
Parallelogramme ( [|-.5.;15.;0.|],[|5.;15.;0.|],[|-.5.;25.;0.|],Uni(Couleur [|0;0;0|]));
Parallelogramme ( [|5.;15.;0.|],[|15.;15.;0.|],[|5.;25.;0.|],Uni (Couleur [|254;254;254|]));
Parallelogramme ( [|15.;15.;0.|],[|25.;15.;0.|],[|15.;25.;0.|],Uni(Couleur [|0;0;0|]));
(*L2*)
Parallelogramme ( [|-.25.;5.;0.|],[|-.15.;5.;0.|],[|-.25.;15.;0.|],Uni (Couleur [|254;254;254|]));
Parallelogramme ( [|-.15.;5.;0.|],[|-.5.;5.;0.|],[|-.15.;15.;0.|],Uni(Couleur [|0;0;0|]));
Parallelogramme ( [|-.5.;5.;0.|],[|5.;5.;0.|],[|-.5.;15.;0.|],Uni (Couleur [|254;254;254|]));
Parallelogramme ( [|5.;5.;0.|],[|15.;5.;0.|],[|5.;15.;0.|],Uni(Couleur [|0;0;0|]));
Parallelogramme ( [|15.;5.;0.|],[|25.;5.;0.|],[|15.;15.;0.|],Uni (Couleur [|254;254;254|]));
(*L3*)
Parallelogramme ( [|-.25.;-.5.;0.|],[|-.15.;-.5.;0.|],[|-.25.;5.;0.|],Uni(Couleur [|0;0;0|]));
Parallelogramme ( [|-.15.;-.5.;0.|],[|-.5.;-.5.;0.|],[|-.15.;5.;0.|],Uni (Couleur [|254;254;254|]));
Parallelogramme ( [|-.5.;-.5.;0.|],[|5.;-.5.;0.|],[|-.5.;5.;0.|],Uni(Couleur [|0;0;0|]));
Parallelogramme ( [|5.;-.5.;0.|],[|15.;-.5.;0.|],[|5.;5.;0.|],Uni (Couleur [|254;254;254|]));
Parallelogramme ( [|15.;-.5.;0.|],[|25.;-.5.;0.|],[|15.;5.;0.|],Uni(Couleur [|0;0;0|]));
(*L4*)
Parallelogramme ( [|-.25.;-.15.;0.|],[|-.15.;-.15.;0.|],[|-.25.;-.5.;0.|],Uni (Couleur [|254;254;254|]));
Parallelogramme ( [|-.15.;-.15.;0.|],[|-.5.;-.15.;0.|],[|-.15.;-.5.;0.|],Uni(Couleur [|0;0;0|]));
Parallelogramme ( [|-.5.;-.15.;0.|],[|5.;-.15.;0.|],[|-.5.;-.5.;0.|],Uni (Couleur [|254;254;254|]));
Parallelogramme ( [|5.;-.15.;0.|],[|15.;-.15.;0.|],[|5.;-.5.;0.|],Uni(Couleur [|0;0;0|]));
Parallelogramme ( [|15.;-.15.;0.|],[|25.;-.15.;0.|],[|15.;-.5.;0.|],Uni (Couleur [|254;254;254|]));
(*L5*)
Parallelogramme ( [|-.25.;-.25.;0.|],[|-.15.;-.25.;0.|],[|-.25.;-.15.;0.|],Uni(Couleur [|0;0;0|]));
Parallelogramme ( [|-.15.;-.25.;0.|],[|-.5.;-.25.;0.|],[|-.15.;-.15.;0.|],Uni (Couleur [|254;254;254|]));
Parallelogramme ( [|-.5.;-.25.;0.|],[|5.;-.25.;0.|],[|-.5.;-.15.;0.|],Uni(Couleur [|0;0;0|]));
Parallelogramme ( [|5.;-.25.;0.|],[|15.;-.25.;0.|],[|5.;-.15.;0.|],Uni (Couleur [|254;254;254|]));
Parallelogramme ( [|15.;-.25.;0.|],[|25.;-.25.;0.|],[|15.;-.15.;0.|],Uni(Couleur [|0;0;0|]));
Sphere ([|16.5;44.5;35.|],3., Uni (Couleur [|254;254;254|]));

(*miroirs*)

Cylindre_vert ([|-82.;0.;0.|],7.5,25.,Uni (Couleur [|0;0;0|]));
Sphere ([|-82.;0.;40.|],20., Uni (Couleur [|125;125;125|]));

Cylindre_vert ([|0.;82.;0.|],7.5,25.,Uni (Couleur [|0;0;0|]));
Sphere ([|0.;82.;40.|],20., Uni (Couleur [|125;125;125|]));

Cylindre_vert ([|0.;-82.;0.|],7.5,25.,Uni (Couleur [|0;0;0|]));
Sphere ([|0.;-82.;40.|],20., Uni (Couleur [|125;125;125|]));

(* luminaires *)

Cylindre_vert ([|16.5;44.5;0.|],5.,20.,Uni (Couleur [|125;125;125|]) );
Disque ([|0.;0.;1.;-.20.|],[|16.5;44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|16.5;44.5;35.|],3., Uni (Couleur [|254;254;254|]));

Cylindre_vert ([|-.16.5;44.5;0.|],5.,20.,Uni (Couleur [|125;125;125|]));
Disque ([|0.;0.;1.;-.20.|],[|-.16.5;44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.16.5;44.5;35.|],3., Uni (Couleur [|254;254;254|]));


Cylindre_vert ([|16.5;-.44.5;0.|],5.,20.,Uni (Couleur [|125;125;125|]));
Disque ([|0.;0.;1.;-.20.|],[|16.5;-.44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|16.5;-.44.5;35.|],3., Uni (Couleur [|254;254;254|]));

Cylindre_vert ([|-.16.5;-.44.5;0.|],5.,20.,Uni (Couleur [|125;125;125|]));
Disque ([|0.;0.;1.;-.20.|],[|-.16.5;-.44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.16.5;-.44.5;35.|],3., Uni (Couleur [|254;254;254|]));


Cylindre_vert ([|-.44.5;16.5;0.|],5.,20.,Uni (Couleur [|125;125;125|]));
Disque ([|0.;0.;1.;-.20.|],[|-.44.5;16.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.44.5;16.5;35.|],3., Uni (Couleur [|254;254;254|]));

Cylindre_vert ([|-.44.5;-.16.5;0.|],5.,20.,Uni (Couleur [|125;125;125|]));
Disque ([|0.;0.;1.;-.20.|],[|-.44.5;-.16.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.44.5;-.16.5;35.|],3., Uni (Couleur [|254;254;254|]))  ];;*)


(*Rendu 2*)

(*let scene_finale = 
( (*escalier*)
prepare_scene 
[Boite ([|44.5;-.45.;0.|],[|99.5;-.45.;0.|],[|44.5;45.;0.|],[|44.5;-.45.;10.|],Uni(Couleur [|72;72;72|]));
Boite ([|56.1;-.35.;10.|],[|99.5;-.35.;10.|],[|56.1;35.;10.|],[|56.1;-.35.;20.|],Uni (Couleur [|72;72;72|]));
Boite ([|67.9;-.27.5;20.|],[|99.5;-.27.5;20.|],[|67.9;27.5;20.|],[|67.9;-.27.5;30.|],Uni(Couleur [|72;72;72|]));
Boite ([|79.5;-.22.5;30.|],[|99.5;-.22.5;30.|],[|79.5;22.5;30.|],[|79.5;-.22.5;40.|],Uni (Couleur [|72;72;72|]));
Face (Parallelogramme ([|44.5;-.45.;10.01|],[|99.5;-.45.;10.01|],[|44.5;45.;10.01|],Uni(Couleur [|32;32;32|])));
Face (Parallelogramme ([|56.1;-.35.;20.01|],[|99.5;-.35.;20.01|],[|56.1;35.;20.01|],Uni(Couleur [|32;32;32|])));
Face (Parallelogramme ([|67.9;-.27.5;30.01|],[|99.5;-.27.5;30.01|],[|67.9;27.5;30.01|],Uni(Couleur [|32;32;32|])));
Face (Parallelogramme ([|79.5;-.22.5;40.01|],[|99.5;-.22.5;40.01|],[|79.5;22.5;40.01|],Uni(Couleur [|32;32;32|])));

(*porte*)
Boite ([|99.;-.20.;40.|],[|100.;-.20.;40.|],[|99.;20.;40.|],[|99.;-.20.;100.|],Minecraft (1,1.,(minecraft_noise [|40;15;0|]    [|0;0;0|] 1)));
Face (Sphere ([|100.;0.;70.|],3., Uni (Couleur [|255;215;0|])));
Face (Sphere ([|100.;10.;80.|],3.,Lum 60.));
Face (Sphere ([|100.;-.10.;80.|],3.,Lum 60.))]

)
@ 
[ (*sol*)
Parallelogramme ( [|-.99.5;-.99.5;-.0.25|],[|99.5;-.99.5;-.0.25|],[|-.99.5;99.5;-.0.25|],Minecraft (1,1.,(minecraft_noise [|192;184;112|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.44.5;-.44.5;-.0.1|],[|44.5;-.44.5;-.0.1|],[|-.44.5;44.5;-.0.1|], Minecraft (1,1.,(minecraft_noise [|46;153;0|]    [|0;0;0|] 1)));
(*murs*)
Parallelogramme ( [|-.99.5;-.99.5;-.0.5|],[|99.5;-.99.5;-.0.5|],[|-.99.5;-.99.5;500.|],Minecraft (1,1.,(minecraft_noise [|175;112;50|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.99.5;-.99.5;-.0.5|],[|-.99.5;99.5;-.0.5|],[|-.99.5;-.99.5;500.|],Minecraft (1,1.,(minecraft_noise [|175;112;50|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.99.5;99.5;-.0.5|],[|99.5;99.5;-.0.5|],[|-.99.5;99.5;500.|],Minecraft (1,1.,(minecraft_noise [|175;112;50|]    [|0;0;0|] 1)));
Parallelogramme ( [|99.5;-.99.5;-.0.5|],[|99.5;100.;-.0.5|],[|99.5;-.99.5;500.|],Minecraft (1,1.,(minecraft_noise [|175;112;50|]    [|0;0;0|] 1)));
(*damier...*)
(*L1*)
Parallelogramme ( [|-.25.;15.;0.|],[|-.15.;15.;0.|],[|-.25.;25.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.15.;15.;0.|],[|-.5.;15.;0.|],[|-.15.;25.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.5.;15.;0.|],[|5.;15.;0.|],[|-.5.;25.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|5.;15.;0.|],[|15.;15.;0.|],[|5.;25.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|15.;15.;0.|],[|25.;15.;0.|],[|15.;25.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
(*L2*)
Parallelogramme ( [|-.25.;5.;0.|],[|-.15.;5.;0.|],[|-.25.;15.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.15.;5.;0.|],[|-.5.;5.;0.|],[|-.15.;15.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.5.;5.;0.|],[|5.;5.;0.|],[|-.5.;15.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|5.;5.;0.|],[|15.;5.;0.|],[|5.;15.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|15.;5.;0.|],[|25.;5.;0.|],[|15.;15.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
(*L3*)
Parallelogramme ( [|-.25.;-.5.;0.|],[|-.15.;-.5.;0.|],[|-.25.;5.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.15.;-.5.;0.|],[|-.5.;-.5.;0.|],[|-.15.;5.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.5.;-.5.;0.|],[|5.;-.5.;0.|],[|-.5.;5.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|5.;-.5.;0.|],[|15.;-.5.;0.|],[|5.;5.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|15.;-.5.;0.|],[|25.;-.5.;0.|],[|15.;5.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
(*L4*)
Parallelogramme ( [|-.25.;-.15.;0.|],[|-.15.;-.15.;0.|],[|-.25.;-.5.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.15.;-.15.;0.|],[|-.5.;-.15.;0.|],[|-.15.;-.5.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.5.;-.15.;0.|],[|5.;-.15.;0.|],[|-.5.;-.5.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|5.;-.15.;0.|],[|15.;-.15.;0.|],[|5.;-.5.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|15.;-.15.;0.|],[|25.;-.15.;0.|],[|15.;-.5.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
(*L5*)
Parallelogramme ( [|-.25.;-.25.;0.|],[|-.15.;-.25.;0.|],[|-.25.;-.15.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.15.;-.25.;0.|],[|-.5.;-.25.;0.|],[|-.15.;-.15.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.5.;-.25.;0.|],[|5.;-.25.;0.|],[|-.5.;-.15.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|5.;-.25.;0.|],[|15.;-.25.;0.|],[|5.;-.15.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|15.;-.25.;0.|],[|25.;-.25.;0.|],[|15.;-.15.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Sphere ([|16.5;44.5;35.|],3., Uni (Couleur [|254;254;254|]));

(*miroirs*)

Cylindre_vert ([|-82.;0.;0.|],7.5,25.,Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Sphere ([|-82.;0.;40.|],20., Uni (Couleur [|125;125;125|]));

Cylindre_vert ([|0.;82.;0.|],7.5,25.,Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Sphere ([|0.;82.;40.|],20., Uni (Couleur [|125;125;125|]));

Cylindre_vert ([|0.;-82.;0.|],7.5,25.,Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Sphere ([|0.;-82.;40.|],20., Uni (Couleur [|125;125;125|]));

(* luminaires *)

Cylindre_vert ([|16.5;44.5;0.|],5.,20.,Minecraft (1,1.,(minecraft_noise [|125;125;125|]    [|0;0;0|] 1)));
Disque ([|0.;0.;1.;-.20.|],[|16.5;44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|16.5;44.5;35.|],3.,Lum 60.);

Cylindre_vert ([|-.16.5;44.5;0.|],5.,20.,Minecraft (1,1.,(minecraft_noise [|125;125;125|]    [|0;0;0|] 1)));
Disque ([|0.;0.;1.;-.20.|],[|-.16.5;44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.16.5;44.5;35.|],3.,Lum 60.);


Cylindre_vert ([|16.5;-.44.5;0.|],5.,20.,Minecraft (1,1.,(minecraft_noise [|125;125;125|]    [|0;0;0|] 1)));
Disque ([|0.;0.;1.;-.20.|],[|16.5;-.44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|16.5;-.44.5;35.|],3.,Lum 60.);

Cylindre_vert ([|-.16.5;-.44.5;0.|],5.,20.,Minecraft (1,1.,(minecraft_noise [|125;125;125|]    [|0;0;0|] 1)));
Disque ([|0.;0.;1.;-.20.|],[|-.16.5;-.44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.16.5;-.44.5;35.|],3.,Lum 60.);


Cylindre_vert ([|-.44.5;16.5;0.|],5.,20.,Minecraft (1,1.,(minecraft_noise [|125;125;125|]    [|0;0;0|] 1)));
Disque ([|0.;0.;1.;-.20.|],[|-.44.5;16.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.44.5;16.5;35.|],3.,Lum 60.);

Cylindre_vert ([|-.44.5;-.16.5;0.|],5.,20.,Minecraft (1,1.,(minecraft_noise [|125;125;125|]    [|0;0;0|] 1)));
Disque ([|0.;0.;1.;-.20.|],[|-.44.5;-.16.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.44.5;-.16.5;35.|],3.,Lum 60.)  ];;*)


(*Rendu 3*)


(*let scene_finale = 
( (*escalier*)
prepare_scene 
[Boite ([|44.5;-.45.;0.|],[|99.5;-.45.;0.|],[|44.5;45.;0.|],[|44.5;-.45.;10.|],Uni(Couleur [|72;72;72|]));
Boite ([|56.1;-.35.;10.|],[|99.5;-.35.;10.|],[|56.1;35.;10.|],[|56.1;-.35.;20.|],Uni (Couleur [|72;72;72|]));
Boite ([|67.9;-.27.5;20.|],[|99.5;-.27.5;20.|],[|67.9;27.5;20.|],[|67.9;-.27.5;30.|],Uni(Couleur [|72;72;72|]));
Boite ([|79.5;-.22.5;30.|],[|99.5;-.22.5;30.|],[|79.5;22.5;30.|],[|79.5;-.22.5;40.|],Uni (Couleur [|72;72;72|]));
Face (Parallelogramme ([|44.5;-.45.;10.01|],[|99.5;-.45.;10.01|],[|44.5;45.;10.01|],Uni(Couleur [|32;32;32|])));
Face (Parallelogramme ([|56.1;-.35.;20.01|],[|99.5;-.35.;20.01|],[|56.1;35.;20.01|],Uni(Couleur [|32;32;32|])));
Face (Parallelogramme ([|67.9;-.27.5;30.01|],[|99.5;-.27.5;30.01|],[|67.9;27.5;30.01|],Uni(Couleur [|32;32;32|])));
Face (Parallelogramme ([|79.5;-.22.5;40.01|],[|99.5;-.22.5;40.01|],[|79.5;22.5;40.01|],Uni(Couleur [|32;32;32|])));

(*porte*)
Boite ([|99.;-.20.;40.|],[|100.;-.20.;40.|],[|99.;20.;40.|],[|99.;-.20.;100.|],Minecraft (1,1.,(minecraft_noise [|40;15;0|]    [|0;0;0|] 1)));
Face (Sphere ([|100.;0.;70.|],3., Uni (Couleur [|255;215;0|])));
Face (Sphere ([|100.;10.;80.|],3.,Lum 60.));
Face (Sphere ([|100.;-.10.;80.|],3.,Lum 60.))]

)
@ 
[ (*sol*)
Parallelogramme ( [|-.99.5;-.99.5;-.0.25|],[|99.5;-.99.5;-.0.25|],[|-.99.5;99.5;-.0.25|],Minecraft (1,1.,(minecraft_noise [|192;184;112|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.44.5;-.44.5;-.0.1|],[|44.5;-.44.5;-.0.1|],[|-.44.5;44.5;-.0.1|], Minecraft (1,1.,(minecraft_noise [|46;153;0|]    [|0;0;0|] 1)));
(*murs*)
Parallelogramme ( [|-.99.5;-.99.5;-.0.5|],[|99.5;-.99.5;-.0.5|],[|-.99.5;-.99.5;500.|],Minecraft (1,1.,(minecraft_noise [|175;112;50|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.99.5;-.99.5;-.0.5|],[|-.99.5;99.5;-.0.5|],[|-.99.5;-.99.5;500.|],Minecraft (1,1.,(minecraft_noise [|175;112;50|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.99.5;99.5;-.0.5|],[|99.5;99.5;-.0.5|],[|-.99.5;99.5;500.|],Minecraft (1,1.,(minecraft_noise [|175;112;50|]    [|0;0;0|] 1)));
Parallelogramme ( [|99.5;-.99.5;-.0.5|],[|99.5;100.;-.0.5|],[|99.5;-.99.5;500.|],Minecraft (1,1.,(minecraft_noise [|175;112;50|]    [|0;0;0|] 1)));
(*damier...*)
(*L1*)
Parallelogramme ( [|-.25.;15.;0.|],[|-.15.;15.;0.|],[|-.25.;25.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.15.;15.;0.|],[|-.5.;15.;0.|],[|-.15.;25.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.5.;15.;0.|],[|5.;15.;0.|],[|-.5.;25.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|5.;15.;0.|],[|15.;15.;0.|],[|5.;25.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|15.;15.;0.|],[|25.;15.;0.|],[|15.;25.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
(*L2*)
Parallelogramme ( [|-.25.;5.;0.|],[|-.15.;5.;0.|],[|-.25.;15.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.15.;5.;0.|],[|-.5.;5.;0.|],[|-.15.;15.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.5.;5.;0.|],[|5.;5.;0.|],[|-.5.;15.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|5.;5.;0.|],[|15.;5.;0.|],[|5.;15.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|15.;5.;0.|],[|25.;5.;0.|],[|15.;15.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
(*L3*)
Parallelogramme ( [|-.25.;-.5.;0.|],[|-.15.;-.5.;0.|],[|-.25.;5.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.15.;-.5.;0.|],[|-.5.;-.5.;0.|],[|-.15.;5.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.5.;-.5.;0.|],[|5.;-.5.;0.|],[|-.5.;5.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|5.;-.5.;0.|],[|15.;-.5.;0.|],[|5.;5.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|15.;-.5.;0.|],[|25.;-.5.;0.|],[|15.;5.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
(*L4*)
Parallelogramme ( [|-.25.;-.15.;0.|],[|-.15.;-.15.;0.|],[|-.25.;-.5.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.15.;-.15.;0.|],[|-.5.;-.15.;0.|],[|-.15.;-.5.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.5.;-.15.;0.|],[|5.;-.15.;0.|],[|-.5.;-.5.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|5.;-.15.;0.|],[|15.;-.15.;0.|],[|5.;-.5.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|15.;-.15.;0.|],[|25.;-.15.;0.|],[|15.;-.5.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
(*L5*)
Parallelogramme ( [|-.25.;-.25.;0.|],[|-.15.;-.25.;0.|],[|-.25.;-.15.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.15.;-.25.;0.|],[|-.5.;-.25.;0.|],[|-.15.;-.15.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|-.5.;-.25.;0.|],[|5.;-.25.;0.|],[|-.5.;-.15.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Parallelogramme ( [|5.;-.25.;0.|],[|15.;-.25.;0.|],[|5.;-.15.;0.|],Minecraft (1,1.,(minecraft_noise [|254;254;254|]    [|0;0;0|] 1)));
Parallelogramme ( [|15.;-.25.;0.|],[|25.;-.25.;0.|],[|15.;-.15.;0.|],Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Sphere ([|16.5;44.5;35.|],3., Uni (Couleur [|254;254;254|]));

(*miroirs*)

Cylindre_vert ([|-82.;0.;0.|],7.5,25.,Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Sphere ([|-82.;0.;40.|],20., Uni (Reflexion));

Cylindre_vert ([|0.;82.;0.|],7.5,25.,Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Sphere ([|0.;82.;40.|],20., Uni (Reflexion));

Cylindre_vert ([|0.;-82.;0.|],7.5,25.,Minecraft (1,1.,(minecraft_noise [|0;0;0|]    [|0;0;0|] 1)));
Sphere ([|0.;-82.;40.|],20., Uni (Reflexion));

(* luminaires *)

Cylindre_vert ([|16.5;44.5;0.|],5.,20.,Minecraft (1,1.,(minecraft_noise [|125;125;125|]    [|0;0;0|] 1)) );
Disque ([|0.;0.;1.;-.20.|],[|16.5;44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|16.5;44.5;35.|],3.,Lum 60.);

Cylindre_vert ([|-.16.5;44.5;0.|],5.,20.,Minecraft (1,1.,(minecraft_noise [|125;125;125|]    [|0;0;0|] 1)));
Disque ([|0.;0.;1.;-.20.|],[|-.16.5;44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.16.5;44.5;35.|],3.,Lum 60.);


Cylindre_vert ([|16.5;-.44.5;0.|],5.,20.,Minecraft (1,1.,(minecraft_noise [|125;125;125|]    [|0;0;0|] 1)));
Disque ([|0.;0.;1.;-.20.|],[|16.5;-.44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|16.5;-.44.5;35.|],3.,Lum 60.);

Cylindre_vert ([|-.16.5;-.44.5;0.|],5.,20.,Minecraft (1,1.,(minecraft_noise [|125;125;125|]    [|0;0;0|] 1)));
Disque ([|0.;0.;1.;-.20.|],[|-.16.5;-.44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.16.5;-.44.5;35.|],3.,Lum 60.);


Cylindre_vert ([|-.44.5;16.5;0.|],5.,20.,Minecraft (1,1.,(minecraft_noise [|125;125;125|]    [|0;0;0|] 1)));
Disque ([|0.;0.;1.;-.20.|],[|-.44.5;16.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.44.5;16.5;35.|],3.,Lum 60.);

Cylindre_vert ([|-.44.5;-.16.5;0.|],5.,20.,Minecraft (1,1.,(minecraft_noise [|125;125;125|]    [|0;0;0|] 1)));
Disque ([|0.;0.;1.;-.20.|],[|-.44.5;-.16.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.44.5;-.16.5;35.|],3.,Lum 60.)  ];;*)

(* Rendus 4 et 5 *)

(* Textures du rendu 4 *)

(*let herbe =         Minecraft (periode_mine,taille_mine,(minecraft_noise [|51;153;0|]    [|5;5;5|] periode_mine))
and sable =         Minecraft (periode_mine,taille_mine,(minecraft_noise [|240;230;140|] [|5;5;5|] periode_mine))
and roche1 =        Minecraft (periode_mine,taille_mine,(minecraft_noise [|32;32;32|] [|5;5;5|] periode_mine))
and roche2 =        Minecraft (periode_mine,taille_mine,(minecraft_noise [|100;100;100|] [|5;5;5|] periode_mine))
and marbre_blanc =  Minecraft (periode_mine,taille_mine,(minecraft_noise [|220;220;220|] [|5;5;5|] periode_mine))
and marbre_noir =   Minecraft (periode_mine,taille_mine,(minecraft_noise [|30;30;30|] [|5;5;5|] periode_mine))
and marbre_colonneb=Minecraft (1,1.,[|[|[|125;125;125|]|]|])
and marbre_colonnen=Minecraft (1,1.,[|[|[|0;0;0|]|]|])
and bois =          Minecraft (periode_mine,taille_mine,(minecraft_noise [|40;15;0|] [|5;5;5|] periode_mine));;
let briques =  (  
  let temp = minecraft_noise [|175;112;50|] [|5;5;5|] 2000 in
  for j = 0 to 200 do
    let ligne = if j<200 then j*10 else j*10 - 5 in
    for j1 = 0 to 1 do
      for i=0 to 1999 do
	temp.(i).(ligne + j1) <- [|0;0;0|]
      done
    done;
    if j<200
    then
      let c = ref 0 in
      while (!c*20 + 10*(j mod 2)) < 2000 do
	for i = 0 to 1 do
	  for j1 = 0 to 9 do
	    temp.((!c*20 + 10*(j mod 2)) + i).(ligne + j1) <- [|0;0;0|]
	  done
	done;
	c:= !c+1
      done
    else ();
  done;
  Minecraft (2000,taille_mine,(temp))
);;*)


(* Textures du rendu 5 *)

let taille_perlin = 0.1 and fact = 50.;;
let sable =           Minecraft (2000,taille_perlin,(perlin_cos_minecraft [|192;184;112|]  fact 25 2000 2000 1.9 0.7))
and herbe=            Minecraft (1000,taille_perlin,(perlin_cos_minecraft [|46;153;0|]  fact 20 1000 1000 1.5 0.7))
and torche_feu=       Minecraft (20,taille_perlin,(perlin_cos_minecraft [|239;140;0|]  fact 10 20 20 1.5 0.7))
and marbre_blanc =    Minecraft (100,taille_perlin,(perlin_colonne 30 0.8 12 100 0.75 100 0.7  [|[|200;200;200|]; [|245;245;245|] |]))
and marbre_noir =     Minecraft (100,taille_perlin,(perlin_colonne 30 0.8 12 100 0.75 100 0.7  [|[|16;16;16|]; [|40;40;40|] |]))
and marbre_colonneb = Minecraft (120,taille_perlin,(perlin_colonne 30 0. 12 120 0.9 120 0.7  [|[|140;140;140|]; [|245;245;245|] |]))
and marbre_colonnen = Minecraft (300,taille_perlin,(perlin_colonne 30 0. 12 300 0.9 300 0.7   [|[|16;16;16|]; [|40;40;40|] |]))
and bois =            Minecraft (500,taille_perlin,(perlin_colonne 30 0.2 12 500 1. 500 0.7  [|[|40;15;0|]; [|19;0;0|] |]))
and roche1 =          Minecraft (1000,taille_perlin,(perlin_cos_minecraft [|32;32;32|]  fact 10 1000 1000 1. 0.7))
and roche2 =          Minecraft (1000,taille_perlin,(perlin_cos_minecraft [|100;100;100|]  fact 10 1000 1000 1. 0.7))
and briques =  (  
  let temp =  perlin_cos_minecraft [|175;112;50|]  (3.*.fact) 25 2000 2000 1. 0.7 in
  for j = 0 to 20 do
    let ligne = if j<20 then j*100 else j*100 - 7 in
    for j1 = 0 to 6 do
      for i=0 to 1999 do
	temp.(i).(ligne + j1) <- [|0;0;0|]
      done
    done;
    if j<20
    then
      let c = ref 0 in
      while (!c*200 + 100*(j mod 2)) < 2000 do
	for i = 0 to 6 do
	  for j1 = 0 to 99 do
	    temp.((!c*200 + 100*(j mod 2)) + i).(ligne + j1) <- [|0;0;0|]
	  done
	done;
	c:= !c+1
      done
    else ();
  done;
  Minecraft (2000,taille_perlin,(temp))
);;


let scene_finale = 
( (*escalier*)
prepare_scene 
[Boite ([|44.5;-.45.;0.|],[|99.5;-.45.;0.|],[|44.5;45.;0.|],[|44.5;-.45.;10.|],roche2);
Boite ([|56.1;-.35.;10.|],[|99.5;-.35.;10.|],[|56.1;35.;10.|],[|56.1;-.35.;20.|],roche2);
Boite ([|67.9;-.27.5;20.|],[|99.5;-.27.5;20.|],[|67.9;27.5;20.|],[|67.9;-.27.5;30.|],roche2);
Boite ([|79.5;-.22.5;30.|],[|99.5;-.22.5;30.|],[|79.5;22.5;30.|],[|79.5;-.22.5;40.|],roche2);
Face (Parallelogramme ([|44.5;-.45.;10.01|],[|99.5;-.45.;10.01|],[|44.5;45.;10.01|],roche1));
Face (Parallelogramme ([|56.1;-.35.;20.01|],[|99.5;-.35.;20.01|],[|56.1;35.;20.01|],roche1));
Face (Parallelogramme ([|67.9;-.27.5;30.01|],[|99.5;-.27.5;30.01|],[|67.9;27.5;30.01|],roche1));
Face (Parallelogramme ([|79.5;-.22.5;40.01|],[|99.5;-.22.5;40.01|],[|79.5;22.5;40.01|],roche1));
(*porte*)
Boite ([|99.;-.20.;40.|],[|100.;-.20.;40.|],[|99.;20.;40.|],[|99.;-.20.;100.|],bois);
Face (Sphere ([|100.;0.;70.|],3., Uni (Couleur [|255;215;0|])));
Face (Sphere ([|100.;10.;80.|],3.,Lum 30.));
Face (Sphere ([|100.;-.10.;80.|],3., Lum 30.))]

)
@ 
[ (*sol*)
Parallelogramme ( [|-.99.5;-.99.5;-.0.25|],[|99.5;-.99.5;-.0.25|],[|-.99.5;99.5;-.0.25|],sable);
Parallelogramme ( [|-.44.5;-.44.5;-.0.1|],[|44.5;-.44.5;-.0.1|],[|-.44.5;44.5;-.0.1|], herbe);
(*murs*)
Parallelogramme ( [|-.99.5;-.99.5;-.0.5|],[|99.5;-.99.5;-.0.5|],[|-.99.5;-.99.5;500.|],briques);
Parallelogramme ( [|-.99.5;-.99.5;-.0.5|],[|-.99.5;99.5;-.0.5|],[|-.99.5;-.99.5;500.|],briques);
Parallelogramme ( [|-.99.5;99.5;-.0.5|],[|99.5;99.5;-.0.5|],[|-.99.5;99.5;500.|],briques);
Parallelogramme ( [|99.5;-.99.5;-.0.5|],[|99.5;100.;-.0.5|],[|99.5;-.99.5;500.|],briques);
(*damier...*)
(*L1*)
Parallelogramme ( [|-.25.;15.;0.|],[|-.15.;15.;0.|],[|-.25.;25.;0.|],marbre_noir);
Parallelogramme ( [|-.15.;15.;0.|],[|-.5.;15.;0.|],[|-.15.;25.;0.|],marbre_blanc);
Parallelogramme ( [|-.5.;15.;0.|],[|5.;15.;0.|],[|-.5.;25.;0.|],marbre_noir);
Parallelogramme ( [|5.;15.;0.|],[|15.;15.;0.|],[|5.;25.;0.|],marbre_blanc);
Parallelogramme ( [|15.;15.;0.|],[|25.;15.;0.|],[|15.;25.;0.|],marbre_noir);
(*L2*)
Parallelogramme ( [|-.25.;5.;0.|],[|-.15.;5.;0.|],[|-.25.;15.;0.|],marbre_blanc);
Parallelogramme ( [|-.15.;5.;0.|],[|-.5.;5.;0.|],[|-.15.;15.;0.|],marbre_noir);
Parallelogramme ( [|-.5.;5.;0.|],[|5.;5.;0.|],[|-.5.;15.;0.|],marbre_blanc);
Parallelogramme ( [|5.;5.;0.|],[|15.;5.;0.|],[|5.;15.;0.|],marbre_noir);
Parallelogramme ( [|15.;5.;0.|],[|25.;5.;0.|],[|15.;15.;0.|],marbre_blanc);
(*L3*)
Parallelogramme ( [|-.25.;-.5.;0.|],[|-.15.;-.5.;0.|],[|-.25.;5.;0.|],marbre_noir);
Parallelogramme ( [|-.15.;-.5.;0.|],[|-.5.;-.5.;0.|],[|-.15.;5.;0.|],marbre_blanc);
Parallelogramme ( [|-.5.;-.5.;0.|],[|5.;-.5.;0.|],[|-.5.;5.;0.|],marbre_noir);
Parallelogramme ( [|5.;-.5.;0.|],[|15.;-.5.;0.|],[|5.;5.;0.|],marbre_blanc);
Parallelogramme ( [|15.;-.5.;0.|],[|25.;-.5.;0.|],[|15.;5.;0.|],marbre_noir);
(*L4*)
Parallelogramme ( [|-.25.;-.15.;0.|],[|-.15.;-.15.;0.|],[|-.25.;-.5.;0.|],marbre_blanc);
Parallelogramme ( [|-.15.;-.15.;0.|],[|-.5.;-.15.;0.|],[|-.15.;-.5.;0.|],marbre_noir);
Parallelogramme ( [|-.5.;-.15.;0.|],[|5.;-.15.;0.|],[|-.5.;-.5.;0.|],marbre_blanc);
Parallelogramme ( [|5.;-.15.;0.|],[|15.;-.15.;0.|],[|5.;-.5.;0.|],marbre_noir);
Parallelogramme ( [|15.;-.15.;0.|],[|25.;-.15.;0.|],[|15.;-.5.;0.|],marbre_blanc);
(*L5*)
Parallelogramme ( [|-.25.;-.25.;0.|],[|-.15.;-.25.;0.|],[|-.25.;-.15.;0.|],marbre_noir);
Parallelogramme ( [|-.15.;-.25.;0.|],[|-.5.;-.25.;0.|],[|-.15.;-.15.;0.|],marbre_blanc);
Parallelogramme ( [|-.5.;-.25.;0.|],[|5.;-.25.;0.|],[|-.5.;-.15.;0.|],marbre_noir);
Parallelogramme ( [|5.;-.25.;0.|],[|15.;-.25.;0.|],[|5.;-.15.;0.|],marbre_blanc);
Parallelogramme ( [|15.;-.25.;0.|],[|25.;-.25.;0.|],[|15.;-.15.;0.|],marbre_noir);

(*miroirs*)

Cylindre_vert ([|-82.;0.;0.|],7.5,25.,marbre_colonnen);
Sphere ([|-82.;0.;40.|],20., Uni ( Reflexion));

Cylindre_vert ([|0.;82.;0.|],7.5,25.,marbre_colonnen);
Sphere ([|0.;82.;40.|],20., Uni ( Reflexion));

Cylindre_vert ([|0.;-82.;0.|],7.5,25.,marbre_colonnen);
Sphere ([|0.;-82.;40.|],20., Uni ( Reflexion));

(* luminaires *)

Cylindre_vert ([|16.5;44.5;0.|],5.,20.,marbre_colonneb );
Disque ([|0.;0.;1.;-.20.|],[|16.5;44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|16.5;44.5;35.|],3., Lum 60.);

Cylindre_vert ([|-.16.5;44.5;0.|],5.,20.,marbre_colonneb);
Disque ([|0.;0.;1.;-.20.|],[|-.16.5;44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.16.5;44.5;35.|],3., Lum 60.);


Cylindre_vert ([|16.5;-.44.5;0.|],5.,20.,marbre_colonneb);
Disque ([|0.;0.;1.;-.20.|],[|16.5;-.44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|16.5;-.44.5;35.|],3., Lum 60.);

Cylindre_vert ([|-.16.5;-.44.5;0.|],5.,20.,marbre_colonneb);
Disque ([|0.;0.;1.;-.20.|],[|-.16.5;-.44.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.16.5;-.44.5;35.|],3., Lum 60.);


Cylindre_vert ([|-.44.5;16.5;0.|],5.,20.,marbre_colonneb);
Disque ([|0.;0.;1.;-.20.|],[|-.44.5;16.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.44.5;16.5;35.|],3., Lum 60.);

Cylindre_vert ([|-.44.5;-.16.5;0.|],5.,20.,marbre_colonneb);
Disque ([|0.;0.;1.;-.20.|],[|-.44.5;-.16.5;20.|],5.,Uni (Couleur [|50;50;50|]));
Sphere ([|-.44.5;-.16.5;35.|],3., Lum 60.)
];;

(* fin de la définition des exemples *)

boucle hauteur largeur pdv vectnorm scene_finale zoom inclinaison false;;
