-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianTruncatedMomentEnvelopeTail
-- name    : Kyprianou.Ch01.inverseGaussianTruncatedMomentEnvelopeTail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T01:00:18.617251+00:00
-- url     : https://prove2.me/theorems/f9126b5b-51a5-4dc4-9934-d766ba774c16
-- title:
--   Inverse Gaussian pointwise truncated-moment Tail estimate
-- statement:
--   On x>1 the exact inverse-Gaussian Lévy truncated moment is bounded by x^(-3/2). Use min(1,x²)=1, sqrt(2π)≥1 and exp(-b²x/2)≤1.
-- source:
--   Kyprianou 2006 Chapter 1 inverse Gaussian Lévy measure, exact regime-specific inequality.

import Mathlib
open MeasureTheory Set Real ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianTruncatedMomentEnvelopeTail
    (b x : ℝ) (hb : 0 < b) (hx : 0 < x) (hx1 : 1 < x) :
    (min 1 (x ^ 2)) *
      ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2))) ≤ x ^ (-(3 / 2 : ℝ)) := by
  sorry
