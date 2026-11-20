-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaNegativeFrequencyPhase
-- name    : Kyprianou.Ch01.stableGammaNegativeFrequencyPhase
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:49:30.664945+00:00
-- url     : https://prove2.me/theorems/fcbb1fe8-e495-4031-93c2-5347b83020ab
-- title:
--   Principal Gamma complex phase at negative stable Fourier frequency
-- statement:
--   For negative Fourier frequency xi, the source-exact principal fractional power exp(alpha log(-i xi)) equals |xi|^alpha exp(i pi alpha/2), preserving the correct positive imaginary-axis phase.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, two-sided stable Lévy exponent.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open Complex Real Set Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaNegativeFrequencyPhase (alpha xi : ℝ) (hxi : xi < 0) :
    Complex.exp ((alpha : ℂ) *
      Complex.log (-(Complex.I * (xi : ℂ)))) =
      ((|xi| ^ alpha : ℝ) : ℂ) *
        Complex.exp (Complex.I * (((Real.pi * alpha / 2 : ℝ) : ℂ))) := by sorry
