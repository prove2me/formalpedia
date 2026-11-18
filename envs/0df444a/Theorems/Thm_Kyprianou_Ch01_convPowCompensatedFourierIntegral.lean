-- Prove2me | Theorems.Thm_Kyprianou_Ch01_convPowCompensatedFourierIntegral
-- name    : Kyprianou.Ch01.convPowCompensatedFourierIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:14:39.957783+00:00
-- url     : https://prove2.me/theorems/e24a01f0-fff5-45f0-89b0-29146e5f75b9
-- title:
--   Compensated Fourier integral of an arbitrary convolution power of a real probability law
-- statement:
--   For each natural convolution power of any real probability measure, the integral of exp(i ξ x)−1 is equal to the corresponding characteristic-function power minus one. This exact identity converts the logarithmic weighted convolution cluster intensity to its Fourier exponent in Kyprianou Chapter 1 Exercise 1.2(ii).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), convolution cluster characteristic exponent.

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms
open MeasureTheory ProbabilityTheory Complex QueueingFundamentals.MG1
set_option autoImplicit false

theorem Kyprianou.Ch01.convPowCompensatedFourierIntegral
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (n : ℕ) (xi : ℝ) :
    (∫ x : ℝ,
      (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1)
        ∂(QueueingFundamentals.MG1.convPow jumpLaw n)) =
      (charFun jumpLaw xi) ^ n - 1 := by
  sorry
