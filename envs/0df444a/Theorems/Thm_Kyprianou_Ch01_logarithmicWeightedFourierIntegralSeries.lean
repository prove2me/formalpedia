-- Prove2me | Theorems.Thm_Kyprianou_Ch01_logarithmicWeightedFourierIntegralSeries
-- name    : Kyprianou.Ch01.logarithmicWeightedFourierIntegralSeries
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:15:10.415523+00:00
-- url     : https://prove2.me/theorems/c95219d5-4330-4901-a6ef-d2f0a4ed5e9d
-- title:
--   Compensated Fourier integral of the finite logarithmically weighted countable probability measure sum
-- statement:
--   For any indexed family of real probability measures and nonnegative q less than one, integrating the compensated Fourier kernel against their logarithmically weighted measure sum equals the series of their individual compensated Fourier integrals multiplied by q^(n+1)/(n+1). This is the core justified exchange of countable summation with integration in the finite Lévy intensity of the compound-geometric law.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), logarithmic convolution cluster Lévy exponent.

import Mathlib
open MeasureTheory Complex
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.logarithmicWeightedFourierIntegralSeries
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ν : ℕ → Measure ℝ) (hν : ∀ n : ℕ, IsProbabilityMeasure (ν n))
    (xi : ℝ) :
    (∫ x : ℝ,
      (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1)
        ∂(Measure.sum fun n : ℕ =>
          (ENNReal.ofReal (q ^ (n + 1) / (n + 1 : ℝ))) • ν n)) =
    ∑' n : ℕ,
      ((q ^ (n + 1) / (n + 1 : ℝ) : ℝ) : ℂ) *
      (∫ x : ℝ,
        (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂ν n) := by
  sorry
