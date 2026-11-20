-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableCompensatedFourierNumeratorDerivative
-- name    : Kyprianou.Ch01.stableCompensatedFourierNumeratorDerivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:36:17.413292+00:00
-- url     : https://prove2.me/theorems/65ce6971-1663-4aeb-9196-0c4fa959164b
-- title:
--   Compensated imaginary Fourier numerator has explicit complex derivative over real time
-- statement:
--   The real-parameter derivative of the original complex compensated Fourier numerator exp(i r)−1−i r is exactly i(exp(i r)−1). This gives the u′ factor for an integration-by-parts proof of Kyprianou Chapter 1 stable α∈(1,2) characteristic integral.
-- source:
--   Kyprianou (2006), Chapter 1 stable characteristic exponents; exact real derivative of compensated Fourier numerator.

import Mathlib
open Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableCompensatedFourierNumeratorDerivative
    (r : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        Complex.exp (Complex.I * (t : ℂ)) - 1 -
          Complex.I * (t : ℂ))
      (Complex.I * (Complex.exp (Complex.I * (r : ℂ)) - 1)) r := by
  sorry
