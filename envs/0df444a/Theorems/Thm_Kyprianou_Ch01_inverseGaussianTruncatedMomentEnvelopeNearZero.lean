-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianTruncatedMomentEnvelopeNearZero
-- name    : Kyprianou.Ch01.inverseGaussianTruncatedMomentEnvelopeNearZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T01:00:16.936676+00:00
-- url     : https://prove2.me/theorems/e6cc68b0-9978-4846-9e40-b278b0438695
-- title:
--   Inverse Gaussian pointwise truncated-moment NearZero estimate
-- statement:
--   On 0<x≤1 the exact inverse-Gaussian Lévy truncated moment is bounded by x^(-1/2). Use min(1,x²)=x², sqrt(2π)≥1, and exp(-b²x/2)≤1.
-- source:
--   Kyprianou 2006 Chapter 1 inverse Gaussian Lévy measure, exact regime-specific inequality.

import Mathlib
open MeasureTheory Set Real ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianTruncatedMomentEnvelopeNearZero
    (b x : ℝ) (hb : 0 < b) (hx : 0 < x) (hx1 : x ≤ 1) :
    (min 1 (x ^ 2)) *
      ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2))) ≤ x ^ (-(1 / 2 : ℝ)) := by
  sorry
