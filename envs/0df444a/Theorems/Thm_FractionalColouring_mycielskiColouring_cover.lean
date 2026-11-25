-- Prove2me | Theorems.Thm_FractionalColouring_mycielskiColouring_cover
-- name    : FractionalColouring.mycielskiColouring_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:34:34.352809+00:00
-- url     : https://prove2.me/theorems/76da0fd3-7887-43b8-ace8-0d0613ad9e51
-- title:
--   Fractional Colouring: mycielski Colouring cover
-- statement:
--   The Fractional Colouring construction uses the mycielski Colouring cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L143-L149
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L143-L149

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

theorem FractionalColouring.mycielskiColouring_cover (x : Finset V → ℝ) (t : ℝ) (u : Vertex V) :
    ∑ S ∈ univ.filter (fun S => u ∈ S), mycielskiColouring x t S =
      ∑ s, ((if u ∈ lift s then x s * ((t - 1) / t) else 0) +
        (if u ∈ liftApex s then x s / t else 0)) + (if u ∈ shadows then 1 / t else 0) := by sorry
