-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46GeometricConvolutionLaplaceV2
-- name    : Kyprianou.Ch04.exercise46GeometricConvolutionLaplaceV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:58:20.803417+00:00
-- url     : https://prove2.me/theorems/3e6454ad-c0e5-52ee-8c2d-cbecc342f6fb
-- title:
--   Geometric mixture of convolution powers has resolvent Laplace transform
-- statement:
--   Express the measure as a countable weighted sum. Multiplicativity of the nonnegative Laplace functional gives the geometric series.
-- source:
--   Kyprianou (2006), Exercise 4.6(iii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46GeometricConvolutionLaplaceV2
    (eta nu : Measure Real) [IsProbabilityMeasure eta]
    (r : ENNReal) (s : Real)
    (hLaw : ∀ B : Set Real, MeasurableSet B →
      nu B = ∑' n : Nat, ((1-r)*r^n) *
        ((Nat.rec (Measure.dirac (0 : Real)) (fun _ (m : Measure Real) => m.conv eta) n : Measure Real) B)) :
    (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-s*x)) ∂nu) =
      (1-r) * (1-r*(∫⁻ x : Real, ENNReal.ofReal (Real.exp (-s*x)) ∂eta))⁻¹ := by
  sorry
