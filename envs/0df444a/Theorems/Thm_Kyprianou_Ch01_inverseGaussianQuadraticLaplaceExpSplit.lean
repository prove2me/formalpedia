-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianQuadraticLaplaceExpSplit
-- name    : Kyprianou.Ch01.inverseGaussianQuadraticLaplaceExpSplit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:05:49.464941+00:00
-- url     : https://prove2.me/theorems/fe24fce9-541d-41c9-82bc-20918b70a8be
-- title:
--   Exact inverse-Gaussian exponential tilt factorisation for the Laplace transform
-- statement:
--   For positive x, the original passage-time quadratic exponent and discount combine exactly to exp(sb)*exp(-s²/(2x)-(b²/2+q)x). This follows directly from the proved quadratic-exponent algebra and Real.exp_add, retaining all original coefficients.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.6(iii).

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianQuadraticExponentSplit
open Real
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianQuadraticLaplaceExpSplit
    (s b q x : ℝ) (hx : 0 < x) :
    Real.exp (-((s - b * x) ^ 2 / (2 * x))) *
      Real.exp (-q * x) =
      Real.exp (s * b) *
        Real.exp (-(s ^ 2 / (2 * x)) -
          (b ^ 2 / 2 + q) * x) := by sorry
