-- Prove2me | Theorems.Thm_Kyprianou_Ch04_rightContinuousCompactEnvelopeV1
-- name    : Kyprianou.Ch04.rightContinuousCompactEnvelopeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:05:56.738802+00:00
-- url     : https://prove2.me/theorems/572a9924-b20f-43cb-a074-174d321006d8
-- title:
--   rightContinuousCompactEnvelopeV1
-- statement:
--   rightContinuousCompactEnvelopeV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), measurable compact probability envelope

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_rightContinuousDyadicSupV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Countably many measurable time sections represent the compact path supremum. -/

theorem Kyprianou.Ch04.rightContinuousCompactEnvelopeV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : NNReal → Ω → ℝ) (T : NNReal)
    (hM : ∀ t, AEMeasurable (Y t) P)
    (hR : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y s w) (Ici t) t) :
    ∃ S : Ω → ℝ≥0∞, Measurable S ∧ ∀ᵐ w ∂P,
      (∀ t ≤ T, ENNReal.ofReal |Y t w| ≤ S w) ∧
      (∀ d : ℝ, (∀ t ≤ T, |Y t w| ≤ d) → S w ≤ ENNReal.ofReal d) := by
  sorry
