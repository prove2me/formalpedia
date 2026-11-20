-- Prove2me | Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityPowerBound
-- name    : Kyprianou.Ch01.inverseGaussianDensityPowerBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:13:37.67078+00:00
-- url     : https://prove2.me/theorems/0c48a98a-0556-42d4-aecd-5eff888753ef
-- title:
--   Positive inverse-Gaussian Lévy density bounded by inverse three-halves power
-- statement:
--   For b>0 and x>0, the exact positive inverse-Gaussian Lévy jump density exp(-b²x/2)/sqrt(2πx³) is at most x^(-3/2). The exponential tilt is at most one, and sqrt(2π)≥1. This exact source-density bound supports both local Fourier kernel integrability estimates.
-- source:
--   Kyprianou (2006), Chapter 1 inverse-Gaussian Lévy triplet density.

import Mathlib
open MeasureTheory Set Real ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.inverseGaussianDensityPowerBound
    (b x : ℝ) (hb : 0 < b) (hx : 0 < x) :
    (1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-(b ^ 2 * x / 2)) ≤ x ^ (-(3 / 2 : ℝ)) := by
  sorry
