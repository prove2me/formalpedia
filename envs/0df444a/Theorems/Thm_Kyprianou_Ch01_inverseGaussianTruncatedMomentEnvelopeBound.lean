-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianTruncatedMomentEnvelopeBound
-- name    : Kyprianou.Ch01.inverseGaussianTruncatedMomentEnvelopeBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:57:00.516924+00:00
-- url     : https://prove2.me/theorems/eefcaaff-fd2f-49b9-ba80-d30665dc5a92
-- title:
--   Inverse-Gaussian truncated moment has an integrable half-power envelope
-- statement:
--   For every b,x>0, the exact inverse-Gaussian Lévy density multiplied by min(1,x²) is bounded by x^(-1/2) on 0<x≤1 and by x^(-3/2) on x>1. Uses exp(-b²x/2)≤1 and sqrt(2π)≥1. Both powers form an integrable piecewise envelope. This isolates the pointwise analysis needed for the original Lévy-measure truncated moment.
-- source:
--   Kyprianou (2006) Chapter 1 inverse-Gaussian Lévy measure, exact density and truncated moment.

import Mathlib
open MeasureTheory Set Real ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianTruncatedMomentEnvelopeBound
    (b x : ℝ) (hb : 0 < b) (hx : 0 < x) :
    (min 1 (x ^ 2)) *
      ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2))) ≤
      (if x ≤ 1 then x ^ (-(1 / 2 : ℝ))
        else x ^ (-(3 / 2 : ℝ))) := by
  sorry
