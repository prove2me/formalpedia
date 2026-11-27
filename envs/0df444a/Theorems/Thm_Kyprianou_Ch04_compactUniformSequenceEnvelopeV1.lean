-- Prove2me | Theorems.Thm_Kyprianou_Ch04_compactUniformSequenceEnvelopeV1
-- name    : Kyprianou.Ch04.compactUniformSequenceEnvelopeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:12:32.431452+00:00
-- url     : https://prove2.me/theorems/2d17e8e4-f1c9-52eb-817a-72652b150468
-- title:
--   compactUniformSequenceEnvelopeV1
-- statement:
--   compactUniformSequenceEnvelopeV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), uniform cutoff probability envelope

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_rightContinuousCompactEnvelopeV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Pairwise dyadic envelopes control the limit without requiring its measurability
or right continuity as an additional assumption. -/

theorem Kyprianou.Ch04.compactUniformSequenceEnvelopeV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → NNReal → Ω → ℝ) (X : NNReal → Ω → ℝ) (T : NNReal)
    (hM : ∀ n t, AEMeasurable (Y n t) P)
    (hR : ∀ n, ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y n s w) (Ici t) t)
    (hU : ∀ᵐ w ∂P, ∀ d : ℝ, 0 < d → ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T,
      |Y n t w - X t w| < d) :
    ∃ S : ℕ → Ω → ℝ≥0∞, (∀ n, Measurable (S n)) ∧ ∀ᵐ w ∂P,
      (∀ n t, t ≤ T → ENNReal.ofReal |Y n t w - X t w| ≤ S n w) ∧
      (∀ d : ℝ, 0 < d → ∃ N : ℕ, ∀ n ≥ N, S n w ≤ ENNReal.ofReal d) := by
  sorry
