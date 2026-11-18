-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineRealToLintegral
-- name    : Kyprianou.Ch01.stableAlphaOneCosineRealToLintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T09:36:22.43608+00:00
-- url     : https://prove2.me/theorems/1d98b0e8-12ec-4e66-adc4-d2e374f3b466
-- title:
--   Real-to-extended conversion for cosine integral
-- statement:
--   The original positive-half-line cosine integrand is nonnegative by cos x ≤1 and x²≥0. It is integrable by the already proved exact Chapter 1 integrability theorem. Apply the pinned integral_eq_lintegral_of_nonneg_ae to express its real Bochner integral as the toReal of its extended nonnegative integral.
-- source:
--   Kyprianou (2006), Chapter 1, stable α=1 cosine integral and exact Tonelli representation.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosinePositiveIntegrable
open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCosineRealToLintegral :
    (∫ x in Ioi (0 : ℝ), (1 - Real.cos x) / x ^ 2) =
    (∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal ((1 - Real.cos x) / x ^ 2)).toReal := by
  sorry
