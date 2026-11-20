-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaPositivePowerAntiderivative
-- name    : Kyprianou.Ch01.stableGammaPositivePowerAntiderivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:19:38.379658+00:00
-- url     : https://prove2.me/theorems/5dd8c68d-d923-4c85-b120-8ffb7f15836c
-- title:
--   Derivative of negative power primitive for zero-to-one stable index
-- statement:
--   Real derivative of r^(−alpha)/(−alpha) is r^(−alpha−1), valid for every strictly positive r and 0<alpha<1.
-- source:
--   Kyprianou (2006), Chapter 1, complex stable Gamma deficit integral, source exact analytic half-line integration by parts.

import Mathlib
open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaPositivePowerAntiderivative
    (alpha r : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => t ^ (-alpha) / (-alpha))
      (r ^ (-alpha - 1)) r := by sorry
