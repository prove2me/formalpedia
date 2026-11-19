-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelValueRealPart
-- name    : Kyprianou.Ch01.stableAlphaAboveOneKernelValueRealPart
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T00:54:17.486353+00:00
-- url     : https://prove2.me/theorems/2f2fc2b0-0806-4405-96f1-90d60e033f4b
-- title:
--   Stable alpha>1 compensated Fourier integral exact re projection
-- statement:
--   The original compensated α>1 complex Fourier integral has real component equal to the real component of Gamma(-α) exp(-i πα/2); this is the genuine compensated cosine kernel integral value.
-- source:
--   Kyprianou (2006), Chapter 1 exact compensated stable-alpha Fourier Gamma identity, α∈(1,2), source-faithful projection.

import Mathlib
open MeasureTheory Set Complex Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaAboveOneKernelValueRealPart
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) / ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ)
      ∂volume).re =
      (((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ)))).re := by
  sorry
