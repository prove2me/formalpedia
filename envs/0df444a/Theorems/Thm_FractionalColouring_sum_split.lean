-- Prove2me | Theorems.Thm_FractionalColouring_sum_split
-- name    : FractionalColouring.sum_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:33:58.856812+00:00
-- url     : https://prove2.me/theorems/c1a2f5fc-dfb8-48de-b33c-80ebd074563e
-- title:
--   Fractional Colouring: sum split
-- statement:
--   A sum over a set of Mycielski vertices, split into apex, original and shadow parts.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L39-L47
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L39-L47

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

theorem FractionalColouring.sum_split (S : Finset (Vertex V)) (h : Vertex V → ℝ) :
    ∑ u ∈ S, h u = (if none ∈ S then h none else 0) +
      ∑ v ∈ univ.filter (fun v => original v ∈ S), h (original v) +
      ∑ v ∈ univ.filter (fun v => shadow v ∈ S), h (shadow v) := by sorry
