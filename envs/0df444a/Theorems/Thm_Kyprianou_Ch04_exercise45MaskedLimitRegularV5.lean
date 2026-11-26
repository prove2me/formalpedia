-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45MaskedLimitRegularV5
-- name    : Kyprianou.Ch04.exercise45MaskedLimitRegularV5
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:36:54.881213+00:00
-- url     : https://prove2.me/theorems/36d67214-d292-571b-8763-35cb4eb24151
-- title:
--   Compact uniform limits of measurable right-continuous approximants
-- statement:
--   Compact uniform limits of measurable right-continuous approximants
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii), uniform probability transfer

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45MaskedLimitRegularV5 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℕ → NNReal → Ω → ℝ) (J : NNReal → Ω → ℝ)
    (hm : ∀ n t, AEMeasurable (A n t) P)
    (hr : ∀ᵐ w ∂P, ∀ n t, ContinuousWithinAt (fun s => A n s w) (Ici t) t)
    (hu : ∀ᵐ w ∂P, ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |A n t w - J t w| < δ) :
    (∀ t, AEMeasurable (J t) P) ∧
      (∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => J s w) (Ici t) t) := by
  sorry
