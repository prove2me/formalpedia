-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneImaginaryKernelOdd
-- name    : Kyprianou.Ch01.stableAlphaOneImaginaryKernelOdd
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:26:49.638077+00:00
-- url     : https://prove2.me/theorems/97d7f2c5-c84e-4e64-85b6-6c7997175e52
-- title:
--   Oddness in frequency of the compensated alpha-one sine Lévy kernel
-- statement:
--   For every real z and r, the source compensated sine kernel at frequency −z equals minus its value at z, including the cutoff r<1 and r=0. This gives the imaginary-part symmetry needed to extend the positive-frequency stable alpha-one logarithmic Lévy exponent to negative frequencies.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable Lévy characteristic exponent.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneImaginaryKernelOdd
    (z r : ℝ) :
    (((-z) * r) * (if r < 1 then (1 : ℝ) else 0) -
      Real.sin ((-z) * r)) / r ^ 2 =
      -(((z * r) * (if r < 1 then (1 : ℝ) else 0) -
        Real.sin (z * r)) / r ^ 2) := by
  sorry
