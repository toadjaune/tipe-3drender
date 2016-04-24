open Graphics;;
#load "graphics.cma";;
let taille_finale = 1000;;
let pix = 1;;
let pi = 3.1415;;
let persistance = 1. (*gain en amplitude*);;
let reduction = 0.65 (*réduction du pas*)

let base =  Array.make_matrix taille_finale taille_finale 0;;
let randomization tab = 
	for i = 0 to taille_finale -1 do
		for j = 0 to taille_finale -1 do
			tab.(i).(j) <- Random.int 255
		done
	done;;
randomization base;;
base ;;
let add_matrix t1 t2 =
	for i = 0 to taille_finale -1 do
		for j = 0 to taille_finale -1 do
			t1.(i).(j) <- t1.(i).(j)+t2.(i).(j)
		done
	done;;
let affichage tex =
Graphics.open_graph (" "^(string_of_int (pix*taille_finale))^"x"^(string_of_int (pix*taille_finale)));
	for i=0 to taille_finale -1 do
		for j=0 to taille_finale -1 do
			let coul=tex.(j).(i) in
			Graphics.set_color (Graphics.rgb coul coul coul);
			Graphics.fill_rect (pix*i) (pix*j) pix pix
		done
	done;;
	
(*affichage base;;*)

let interpolation_cos a b x =
	let kx = (1. -. cos ( x *. pi)) /. 2. in
	( (float_of_int a) *. (1. -. kx) +. (float_of_int b) *. kx);;
let inter_cos_carre a b c d x y =  (*carre ABCD*)
	interpolation_cos 
		(int_of_float (interpolation_cos a b x))
		(int_of_float (interpolation_cos d c x))
		y ;;

let perlin_cos amplitude pas base=
let res = Array.make_matrix taille_finale taille_finale 0
	and division =  taille_finale / pas in
		for i = 0 to division  do
			for j = 0 to division  do
				for k = pas*i to min (pas *(i+1) -1) (taille_finale -1 ) do
					for l = pas*j to min (pas*(j+1) -1) (taille_finale -1 ) do
						res.(k).(l) <-int_of_float (amplitude *. 
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

 

let perlin octave pas base=
	let amplitude = ref 1.
	and pas_p = ref pas
	and res = Array.make_matrix taille_finale taille_finale 0 in
		for i = 1 to octave do
			if !pas_p <> 0 then
			(add_matrix res (perlin_cos !amplitude !pas_p base);
			amplitude := !amplitude *. persistance;
			pas_p := int_of_float ( (float_of_int !pas_p) *. reduction) )
			else ()
		done;
		if persistance <> 1. 
		then
		for i = 0 to taille_finale -1 do
			for j = 0 to taille_finale -1 do
				res.(i).(j) <- int_of_float ((float_of_int (res.(i).(j))) /. ((1. -. !amplitude)/.(1. -. persistance))) 
			done
		done
		else
		for i = 0 to taille_finale -1 do
			for j = 0 to taille_finale -1 do
				res.(i).(j) <- (res.(i).(j)) /octave 
			done
		done;
		res;;
(*affichage (perlin 10 taille_finale base);;*)



let base1 =  Array.make_matrix taille_finale taille_finale 0;;
let base2 =  Array.make_matrix taille_finale taille_finale 0;;
let base3 =  Array.make_matrix taille_finale taille_finale 0;;

randomization base1;; 
randomization base2;; 
randomization base3;;

let affichage_rgb t1 t2 t3 = 
Graphics.open_graph (" "^(string_of_int (pix*taille_finale))^"x"^(string_of_int (pix*taille_finale)));
	for i=0 to taille_finale -1 do
		for j=0 to taille_finale -1 do
			Graphics.set_color (Graphics.rgb t1.(i).(j) t2.(i).(j) t3.(i).(j));
			Graphics.fill_rect (pix*i) (pix*j) pix pix
		done
	done;;

(*affichage_rgb 
	(perlin 7 taille_finale base1)
	(perlin 7 taille_finale base2)
	(perlin 7 taille_finale base3);;*)

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
		r,g,b;;

let perlin_cos_minecraft [|r;g;b|] [|coef_r;coef_g;coef_b|] octave=
	let coul = minecraft_noise [|r;g;b|] [|coef_r;coef_g;coef_b|] taille_finale in
		let r,g,b = transfo_minecraft coul
			in (perlin octave taille_finale r),(perlin octave taille_finale g),(perlin octave taille_finale b);;
			
(*let r,g,b = perlin_cos_minecraft [|51;153;0|]  [|15;15;15|] 20 in
	affichage_rgb r g b;;*)
