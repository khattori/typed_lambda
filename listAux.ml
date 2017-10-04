(** リスト操作のための補助関数定義 *)

module List =
struct
  include List

(** リストのフィルターと写像を同時に行う *)
(* filter_map: ('a -> 'b option) -> 'a list -> 'b list *)
let filter_map f xs =
  let rec iter acc = function
    | [] -> rev acc
    | x::xs -> match f x with None -> iter acc xs | Some y -> iter (y::acc) xs
  in
    iter [] xs

(** リストが重複した要素を持っているか調べる *)
(* has_dup: 'a list -> bool *)
let has_dup xs =
  let rec iter = function
    | [] -> false
    | x::xs -> if mem x xs then true else iter xs
  in
    iter xs

(** リストが重複した要素を持っているかチェックする *)
(* check_dup: ('a -> unit) -> 'a list -> unit *)
let check_dup f xs =
  let rec iter = function
    | [] -> ()
    | x::xs -> if mem x xs then f x else iter xs
  in
    iter xs

let rec map2_unb f xs ys =
  match (xs,ys) with
    | xs,[] -> xs
    | (x::xs,y::ys) -> let r = f x y in r::map2_unb f xs ys
    | _ -> invalid_arg "ListAux.map2_unb"

(** 3つのリストを1つのリストに写像する *)
(* map3: ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list *)
let rec map3 f xs ys zs =
  match (xs,ys,zs) with
    | [],[],[] -> []
    | (x::xs,y::ys,z::zs) -> let r = f x y z in r::map3 f xs ys zs
    | _ -> invalid_arg "ListAux.map3"

(* make: (int -> 'a) -> int -> 'a list *)
let make f n =
  let rec iter i ls =
    if i < n then
      iter (i+1) ((f i)::ls)
    else
      ls
  in
    List.rev(iter 0 [])

(* cut: int -> 'a list -> 'a list *)
let rec cut n ls =
    if n <= 0 then ls else cut (n-1) (tl ls)

end

