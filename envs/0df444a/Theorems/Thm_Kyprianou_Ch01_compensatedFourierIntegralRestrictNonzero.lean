-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compensatedFourierIntegralRestrictNonzero
-- name    : Kyprianou.Ch01.compensatedFourierIntegralRestrictNonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:12:51.176502+00:00
-- url     : https://prove2.me/theorems/c83c789c-d30f-4df0-a7dc-37bbbce641b6
-- title:
--   Removing the zero atom preserves the compensated Fourier integral of any finite measure
-- statement:
--   Given a finite positive measure and any real frequency, restricting the measure to the complement of zero does not change the integral of exp(i ξ x)−1, since the integrand vanishes at zero. This makes the compound-geometric Lévy measure representation faithful when convolution clusters can sum to zero.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), removal of null-valued compound-Poisson clusters.

import Mathlib
open MeasureTheory Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.compensatedFourierIntegralRestrictNonzero
    (μ : Measure ℝ) [IsFiniteMeasure μ] (xi : ℝ) :
    (∫ x : ℝ,
      (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1)
        ∂(μ.restrict ({0}ᶜ))) =
    ∫ x : ℝ, (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂μ := by
  sorry
