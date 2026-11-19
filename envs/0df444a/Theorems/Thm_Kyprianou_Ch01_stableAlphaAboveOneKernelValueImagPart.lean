-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelValueImagPart
-- name    : Kyprianou.Ch01.stableAlphaAboveOneKernelValueImagPart
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T00:54:17.720047+00:00
-- url     : https://prove2.me/theorems/ef2910f7-9048-4c54-ac26-98136fa34192
-- title:
--   Stable alpha>1 compensated Fourier integral exact im projection
-- statement:
--   The original compensated α>1 complex Fourier integral has imaginary component equal to the imaginary component of Gamma(-α) exp(-i πα/2); this is the genuine compensated sine kernel integral value.
-- source:
--   Kyprianou (2006), Chapter 1 exact compensated stable-alpha Fourier Gamma identity, α∈(1,2), source-faithful projection.

import Mathlib
open MeasureTheory Set Complex Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneKernelValueImagPart
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) / ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ)
      ∂volume).im =
      (((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ)))).im := by
  sorry
