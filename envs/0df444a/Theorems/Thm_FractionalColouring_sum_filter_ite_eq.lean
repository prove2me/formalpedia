-- Prove2me | Theorems.Thm_FractionalColouring_sum_filter_ite_eq
-- name    : FractionalColouring.sum_filter_ite_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:34:30.293122+00:00
-- url     : https://prove2.me/theorems/9f843288-5332-475e-941b-de94e64478f6
-- title:
--   Fractional Colouring: sum filter ite eq
-- statement:
--   A sum of indicator weights over the sets containing `u`.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L133-L136
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L133-L136

module
public import Definitions.Def_FractionalLib_Basic
public import Definitions.Def_Mycielski_Basic
public import Definitions.Def_FractionalLib_LarsenProppUllman
set_option autoImplicit true
@[expose] public section
public section
open Finset hiding shadow
open Mycielski
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}

theorem FractionalColouring.sum_filter_ite_eq (u : Vertex V) (L : Finset (Vertex V)) (c : ℝ) :
    ∑ S ∈ univ.filter (fun S => u ∈ S), (if S = L then c else 0) = if u ∈ L then c else 0 := by sorry
