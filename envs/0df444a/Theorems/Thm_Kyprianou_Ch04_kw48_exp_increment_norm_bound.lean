-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_exp_increment_norm_bound
-- name    : Kyprianou.Ch04.kw48_exp_increment_norm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:43:58.088131+00:00
-- url     : https://prove2.me/theorems/7de6aed2-353c-5d83-9e4d-9b0e40ceb669
-- title:
--   Global first order complex exponential increment bound
-- statement:
--   Global first order complex exponential increment bound.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
set_option autoImplicit false

/-- A global first-order bound with a real-part cap, using the
quadratic small-increment bound and the elementary large-increment bound. -/

theorem Kyprianou.Ch04.kw48_exp_increment_norm_bound (z : Complex) (K : Real) (hK : 0 ≤ K)
    (hre : (-z).re ≤ K) :
    ‖1-Complex.exp (-z)‖ ≤ 2*Real.exp K*‖z‖ := by sorry
