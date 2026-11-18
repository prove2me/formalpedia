-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseRealKernel
-- name    : Kyprianou.Ch01.stableAlphaOneLogPhaseRealKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:27:56.907683+00:00
-- url     : https://prove2.me/theorems/4cf6a304-0b5f-49d5-b467-e23184b2ae0c
-- title:
--   Exact real-part identity of the compensated index-one complex stable Lévy kernel
-- statement:
--   At every pair of real values z,r, the real part of the complex compensated integrand 1−exp(i z r)+i z r 1_(r<1), divided by r², equals (1−cos(zr))/r². The compensation is purely imaginary. This exact identity separates the real part of the original Chapter 1 index-one stable Lévy exponent from its logarithmic phase calculation.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable Lévy characteristic exponent.

import Mathlib
open MeasureTheory Complex Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLogPhaseRealKernel
    (z r : ℝ) :
    (((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)).re =
      (1 - Real.cos (z * r)) / r ^ 2 := by
  sorry
