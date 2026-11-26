-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45MaskedDominatedUCPV5
-- name    : Kyprianou.Ch04.exercise45MaskedDominatedUCPV5
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T20:36:55.034971+00:00
-- url     : https://prove2.me/theorems/1dda4577-5e95-521b-a30e-24b5d7f2a4f0
-- title:
--   Uniform probability transfer with a vanishing measurable residual
-- statement:
--   Uniform probability transfer with a vanishing measurable residual
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii), uniform probability transfer

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45MaskedDominatedUCPV5 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U A R : ℕ → NNReal → Ω → ℝ) (J : NNReal → Ω → ℝ) (T : NNReal)
    (hm : ∀ n t, AEMeasurable (A n t) P ∧ AEMeasurable (R n t) P)
    (hr : ∀ᵐ w ∂P, ∀ n t,
      ContinuousWithinAt (fun s => A n s w) (Ici t) t ∧
      ContinuousWithinAt (fun s => R n s w) (Ici t) t)
    (hu : ∀ᵐ w ∂P, ∀ L : NNReal, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ L, |A n t w - J t w| < δ)
    (hR : ∀ᵐ w ∂P, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |R n t w| < δ)
    (hb : ∀ᵐ w ∂P, ∀ n t, t ≤ T →
      |U n t w| ≤ |A n t w - J t w| + |R n t w|)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, δ ≤ |U n t w|}).toReal) atTop (nhds 0) := by
  sorry
