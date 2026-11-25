-- Prove2me | Theorems.Thm_FractionalColouring_sum_mycielskiClique
-- name    : FractionalColouring.sum_mycielskiClique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:33:30.807202+00:00
-- url     : https://prove2.me/theorems/85c8d6cc-b24e-5dc7-8461-6800db59874e
-- title:
--   Fractional Colouring: sum mycielski Clique
-- statement:
--   The Fractional Colouring construction uses the sum mycielski Clique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L241-L246
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L241-L246

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

theorem FractionalColouring.sum_mycielskiClique (g : V → ℝ) (a : ℝ) (S : Finset (Vertex V)) :
    ∑ u ∈ S, mycielskiClique g a u = (if none ∈ S then 1 / a else 0) +
      (1 - 1 / a) * ∑ v ∈ univ.filter (fun v => original v ∈ S), g v +
      (∑ v ∈ univ.filter (fun v => shadow v ∈ S), g v) / a := by sorry
