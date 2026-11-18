-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseKernelMeasurable
-- name    : Kyprianou.Ch01.stableAlphaOneLogPhaseKernelMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:40:35.913415+00:00
-- url     : https://prove2.me/theorems/3dc86588-37c4-4e12-adc7-4eec457d6e6e
-- title:
--   Measurability of source-exact compensated stable alpha-one complex Lévy kernel
-- statement:
--   For every real z, the full complex alpha-one compensated kernel with the r<1 indicator is measurable on the real line. This justifies applying Bochner dominated integrability separately near zero, on the middle interval and at infinity.
-- source:
--   Kyprianou (2006), Chapter 1, stable alpha-one Lévy exponent.

import Mathlib
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLogPhaseKernelMeasurable (z : ℝ) :
    Measurable (fun r : ℝ => ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) := by
  sorry
