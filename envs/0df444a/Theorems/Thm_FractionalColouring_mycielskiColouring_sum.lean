-- Prove2me | Theorems.Thm_FractionalColouring_mycielskiColouring_sum
-- name    : FractionalColouring.mycielskiColouring_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:34:37.562734+00:00
-- url     : https://prove2.me/theorems/065dba63-5b74-4775-af26-c15e95cbe1de
-- title:
--   Fractional Colouring: mycielski Colouring sum
-- statement:
--   The Fractional Colouring construction uses the mycielski Colouring sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L151-L155
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L151-L155

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

theorem FractionalColouring.mycielskiColouring_sum (x : Finset V → ℝ) (t : ℝ) :
    ∑ S, mycielskiColouring x t S = ∑ s, x s * ((t - 1) / t) + ∑ s, x s / t + 1 / t := by sorry
