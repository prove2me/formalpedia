-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49RenewalLawSeriesV1
-- name    : Kyprianou.Ch04.exercise49RenewalLawSeriesV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T15:03:47.486975+00:00
-- url     : https://prove2.me/theorems/cd906217-9812-4c32-abfe-6b9d99dbb893
-- title:
--   Defective probability convolution fixed point has a geometric convolution expansion
-- statement:
--   Defective probability convolution fixed point has a geometric convolution expansion
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49RenewalLawSeriesV1
    (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho < 1)
    (mu eta : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure eta]
    (hLaw : mu = ENNReal.ofReal (1 - rho) • Measure.dirac 0 +
      ENNReal.ofReal rho • (mu.conv eta)) (B : Set ℝ) (hB : MeasurableSet B) :
    let convPow : Nat → Measure ℝ :=
      Nat.rec (Measure.dirac (0 : ℝ)) (fun _ nu => nu.conv eta)
    (mu B).toReal = (1 - rho) * ∑' k : Nat, rho ^ k * (convPow k B).toReal := by
  sorry
