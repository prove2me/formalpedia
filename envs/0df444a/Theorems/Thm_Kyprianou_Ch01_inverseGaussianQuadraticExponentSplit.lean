-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianQuadraticExponentSplit
-- name    : Kyprianou.Ch01.inverseGaussianQuadraticExponentSplit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:03:20.941227+00:00
-- url     : https://prove2.me/theorems/fb5f603a-9e14-459d-827b-fec83a2b3069
-- title:
--   Inverse-Gaussian square exponent splits into reciprocal and linear Laplace terms
-- statement:
--   For x>0, expand the source first-passage quadratic exponent and discount exactly as sb - s²/(2x) - (b²/2+q)x. This isolates the inverse-3/2 Gaussian Laplace kernel from the constant drift factor.
-- source:
--   Kyprianou (2006), Exercise 1.6(iii), inverse Gaussian hitting-time Laplace integral.

import Mathlib
open Real
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianQuadraticExponentSplit
    (s b q x : ℝ) (hx : 0 < x) :
    -((s - b * x) ^ 2 / (2 * x)) - q * x =
      s * b - s ^ 2 / (2 * x) - (b ^ 2 / 2 + q) * x := by sorry
