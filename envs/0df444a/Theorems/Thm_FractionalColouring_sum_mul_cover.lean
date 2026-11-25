-- Prove2me | Theorems.Thm_FractionalColouring_sum_mul_cover
-- name    : FractionalColouring.sum_mul_cover
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:29:50.659836+00:00
-- url     : https://prove2.me/theorems/8074e917-9a2e-4cda-8815-a7b3a42d7165
-- title:
--   Fractional Colouring: sum mul cover
-- statement:
--   Exchange of summation for a vertex weighting against a fractional colouring.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L83-L95
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean#L83-L95

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

theorem FractionalColouring.sum_mul_cover (g : V → ℝ) (x : Finset V → ℝ) (T : Finset V) :
    ∑ v ∈ T, g v * ∑ s ∈ univ.filter (fun s => v ∈ s), x s =
      ∑ s, x s * ∑ v ∈ T ∩ s, g v := by sorry
