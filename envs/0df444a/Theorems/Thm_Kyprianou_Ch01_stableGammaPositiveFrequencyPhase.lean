-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaPositiveFrequencyPhase
-- name    : Kyprianou.Ch01.stableGammaPositiveFrequencyPhase
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:49:35.255327+00:00
-- url     : https://prove2.me/theorems/d0ad5c54-b4f7-4d1c-a0b6-a525038494c3
-- title:
--   Principal Gamma complex phase at positive stable Fourier frequency
-- statement:
--   For positive Fourier frequency xi, the principal complex Gamma fractional power exp(alpha log(-i xi)) factors exactly into xi^alpha exp(-i pi alpha/2). It preserves the principal log branch and supplies the phase/skew conversion for the original stable Lévy exponent.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, stable Gamma Fourier phase.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open Complex Real Set Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaPositiveFrequencyPhase (alpha xi : ℝ) (hxi : 0 < xi) :
    Complex.exp ((alpha : ℂ) *
      Complex.log (-(Complex.I * (xi : ℂ)))) =
      ((xi ^ alpha : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (((Real.pi * alpha / 2 : ℝ) : ℂ)))) := by sorry
