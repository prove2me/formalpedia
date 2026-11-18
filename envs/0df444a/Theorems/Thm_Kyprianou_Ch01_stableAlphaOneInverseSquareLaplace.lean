-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneInverseSquareLaplace
-- name    : Kyprianou.Ch01.stableAlphaOneInverseSquareLaplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:16:22.149662+00:00
-- url     : https://prove2.me/theorems/0a3752a3-43eb-4e74-a52a-8ff9122729c1
-- title:
--   Positive Laplace representation of the inverse-square kernel used in the stable cosine integral
-- statement:
--   For every real x>0, the positive-half-line integral of t exp(−xt) is exactly 1/x². This standard Gamma(2) Laplace transform supplies a nonnegative Tonelli kernel for the stable alpha-one cosine Lévy integral: 1/x²=∫₀∞ t e^{−xt}dt. It may be combined with a separate Laplace-cosine integral to reach the proved rational integral π/2.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable cosine Lévy exponent; inverse-square Laplace representation.

import Mathlib
open MeasureTheory Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneInverseSquareLaplace
    (x : ℝ) (hx : 0 < x) :
    (∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-(x * t))) =
      (x ^ 2)⁻¹ := by
  sorry
