-- Prove2me | Theorems.Thm_FractionalColouring_isFracColouring_mycielskiColouring
-- name    : FractionalColouring.isFracColouring_mycielskiColouring
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:34:19.26292+00:00
-- url     : https://prove2.me/theorems/14e5e916-3f37-5de7-a63a-a28753f80802
-- title:
--   Fractional Colouring: is Frac Colouring mycielski Colouring
-- statement:
--   The Fractional Colouring construction uses the is Frac Colouring mycielski Colouring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L157-L213
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean#L157-L213

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

theorem FractionalColouring.isFracColouring_mycielskiColouring {x : Finset V → ℝ} (hx : IsFracColouring G x)
    {t : ℝ} (ht : 1 ≤ t) (hxt : ∑ s, x s = t) :
    IsFracColouring (graph G) (mycielskiColouring x t) := by sorry
