-- Prove2me | Theorems.Thm_FractionalColouring_IsFracClique_sum_le_fracChromaticNumber
-- name    : FractionalColouring.IsFracClique.sum_le_fracChromaticNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:30:06.849437+00:00
-- url     : https://prove2.me/theorems/b883493c-4f27-511f-ae5d-5443039596c9
-- title:
--   Is Frac Clique: sum le frac Chromatic Number
-- statement:
--   A fractional clique weighs at most `χ_f(G)`.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L121-L123
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L121-L123

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Definitions.Def_FractionalLib_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}

theorem FractionalColouring.IsFracClique.sum_le_fracChromaticNumber {g : V → ℝ} (hg : IsFracClique G g) :
    ∑ v, g v ≤ fracChromaticNumber G := by sorry
