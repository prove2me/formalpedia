-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45DyadicDominatedUCPV5
-- name    : Kyprianou.Ch04.exercise45DyadicDominatedUCPV5
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T20:00:08.924201+00:00
-- url     : https://prove2.me/theorems/01e13d5c-3192-4e3e-9ec6-58a4ca214797
-- title:
--   Almost sure uniform convergence transfers via a measurable dyadic dominator
-- statement:
--   Almost sure uniform convergence transfers via a measurable dyadic dominator
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii); dominated uniform probability transfer.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45DyadicDominatedUCPV5 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U V : ℕ → NNReal → Ω → ℝ) (T : NNReal)
    (hm : ∀ n t, AEMeasurable (V n t) P)
    (hr : ∀ᵐ w ∂P, ∀ n t, ContinuousWithinAt (fun s => V n s w) (Ici t) t)
    (hb : ∀ᵐ w ∂P, ∀ n t, t ≤ T → |U n t w| ≤ |V n t w|)
    (hu : ∀ᵐ w ∂P, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |V n t w| < δ)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, δ ≤ |U n t w|}).toReal) atTop (nhds 0) := by
  sorry
