-- Prove2me | Theorems.Thm_Kyprianou_Ch01_expDeficit_hasDerivAt_zero
-- name    : Kyprianou.Ch01.expDeficit_hasDerivAt_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T12:19:56.472197+00:00
-- url     : https://prove2.me/theorems/283a7105-d91f-450a-83c8-2e48ac69e1e1
-- title:
--   Exponential-deficit integrand has derivative equal to the claim size at zero
-- statement:
--   For each real x, differentiation of the exponential-deficit map θ↦1−exp(−θx) at θ=0 gives the derivative x, using the chain rule for the real exponential.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9(i), Laplace exponent's right derivative

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.expDeficit_hasDerivAt_zero
    (x : ℝ) :
    HasDerivAt (fun theta : ℝ => 1 - Real.exp (-theta * x)) x 0 := by sorry
