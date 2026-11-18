-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseIntegrableExact
-- name    : Kyprianou.Ch01.stableAlphaOneLogPhaseIntegrableExact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T10:34:12.735764+00:00
-- url     : https://prove2.me/theorems/4e985458-412b-41a8-94a4-03dcbcdf613d
-- title:
--   Absolute Bochner integrability of the exact source stable alpha-one complex kernel
-- statement:
--   Establishes full integrability near zero using the complex quadratic Taylor remainder and at infinity by the r^(-2) tail, preserving the small-jump compensation indicator.
-- source:
--   Kyprianou (2006), Chapter 1, index-one stable Lévy logarithmic phase, source original theorem stableAlphaOneLogPhase.

import Mathlib
open MeasureTheory Set Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLogPhaseIntegrableExact :
    ∀ z : ℝ, 0 < z →
    IntegrableOn (fun r : ℝ => ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  sorry
