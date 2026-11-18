-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseImaginaryExact
-- name    : Kyprianou.Ch01.stableAlphaOneLogPhaseImaginaryExact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:34:12.938076+00:00
-- url     : https://prove2.me/theorems/2cee017f-e40f-4abd-a623-4cddc7743c37
-- title:
--   Imaginary logarithmic phase of the compensated alpha-one stable Lévy kernel
-- statement:
--   Establishes a common real constant k and the precise imaginary integral z log z−kz for all positive frequencies, retaining the exact source cutoff.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable Lévy logarithmic phase, source original theorem stableAlphaOneLogPhase.

import Mathlib
open MeasureTheory Set Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLogPhaseImaginaryExact :
    ∃ k : ℝ, ∀ z : ℝ, 0 < z →
    (∫ r in Set.Ioi (0 : ℝ), ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume).im =
      z * Real.log z - k * z := by
  sorry
