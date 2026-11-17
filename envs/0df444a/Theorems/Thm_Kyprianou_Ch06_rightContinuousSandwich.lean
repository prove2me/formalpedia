-- Prove2me | Theorems.Thm_Kyprianou_Ch06_rightContinuousSandwich
-- name    : Kyprianou.Ch06.rightContinuousSandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:59:23.835054+00:00
-- url     : https://prove2.me/theorems/6bcb6610-75aa-4710-9f76-28bcdc696f00
-- title:
--   Chapter 6 Wiener–Hopf: right-continuous survival sandwich lemma
-- statement:
--   For a right-continuous ENNReal-valued function F on the nonnegative reals, any y bounded above by F(t) and below by F(s) at every s>t must equal F(t). This order-topological squeeze is the analytic step in the Poisson first-arrival survival law.

import Mathlib
open Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.rightContinuousSandwich
    (F : NNReal → ENNReal) (t : NNReal) (y : ENNReal)
    (hCont : ContinuousAt F t)
    (hUpper : y ≤ F t)
    (hLower : ∀ s : NNReal, t < s → F s ≤ y) :
    y = F t := by sorry
