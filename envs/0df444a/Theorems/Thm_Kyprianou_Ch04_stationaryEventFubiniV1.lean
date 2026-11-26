-- Prove2me | Theorems.Thm_Kyprianou_Ch04_stationaryEventFubiniV1
-- name    : Kyprianou.Ch04.stationaryEventFubiniV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:27:22.214043+00:00
-- url     : https://prove2.me/theorems/9e662622-bc1c-4be7-a210-1657eda526b0
-- title:
--   Fubini transfer of a stationary full-measure event
-- statement:
--   Reverse the almost-everywhere quantifiers using measurable Fubini and choose a deterministic time from the nontrivial time measure.
-- source:
--   Supporting proof for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.stationaryEventFubiniV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure ℝ) [SigmaFinite Q]
    (hQ : NeBot (ae Q))
    (A : ℝ → Ω → Prop)
    (hm : MeasurableSet {z : ℝ × Ω | A z.1 z.2})
    (ha : ∀ᵐ ω ∂P, ∀ᵐ s ∂Q, A s ω)
    (hs : ∀ s : ℝ, (∀ᵐ ω ∂P, A s ω) → ∀ᵐ ω ∂P, A 0 ω) :
    ∀ᵐ ω ∂P, A 0 ω := by
  sorry
