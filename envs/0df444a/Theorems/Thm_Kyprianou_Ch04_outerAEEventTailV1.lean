-- Prove2me | Theorems.Thm_Kyprianou_Ch04_outerAEEventTailV1
-- name    : Kyprianou.Ch04.outerAEEventTailV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:02:01.552657+00:00
-- url     : https://prove2.me/theorems/00b6309c-e7d9-4a0a-9ce8-25df00362118
-- title:
--   outerAEEventTailV1
-- statement:
--   outerAEEventTailV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii), outer probability error transfer

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal Topology
set_option autoImplicit false

/-- A sequence of measurable event envelopes that eventually excludes almost every
sample has vanishing outer probabilities, including for arbitrary subsets. -/

theorem Kyprianou.Ch04.outerAEEventTailV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A B : ℕ → Set Ω)
    (hB : ∀ n, MeasurableSet (B n))
    (hSub : ∀ n, ∀ᵐ w ∂P, w ∈ A n → w ∈ B n)
    (hAE : ∀ᵐ w ∂P, ∃ N : ℕ, ∀ n ≥ N, w ∉ B n) :
    Tendsto (fun n => (P (A n)).toReal) atTop (nhds 0) := by
  sorry
