-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49RenewalConvolutionStepV1
-- name    : Kyprianou.Ch04.exercise49RenewalConvolutionStepV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:05:26.189999+00:00
-- url     : https://prove2.me/theorems/0d2a2937-eb41-5ac2-94d8-4d8644896951
-- title:
--   Convolve the defective renewal law with an arbitrary probability measure
-- statement:
--   One step of convolution iteration of the renewal measure identity, evaluated on a set.
-- source:
--   Kyprianou (2006), Exercise 4.9(iii)

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49RenewalConvolutionStepV1
    (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho < 1)
    (mu eta nu : Measure ℝ) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure eta] [IsProbabilityMeasure nu]
    (hLaw : mu = ENNReal.ofReal (1 - rho) • Measure.dirac 0 +
      ENNReal.ofReal rho • (mu.conv eta)) (B : Set ℝ) :
    (mu.conv nu B).toReal =
      (1 - rho) * (nu B).toReal + rho * (mu.conv (nu.conv eta) B).toReal := by
  sorry
