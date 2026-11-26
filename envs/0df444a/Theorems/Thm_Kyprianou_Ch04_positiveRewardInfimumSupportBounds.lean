-- Prove2me | Theorems.Thm_Kyprianou_Ch04_positiveRewardInfimumSupportBounds
-- name    : Kyprianou.Ch04.positiveRewardInfimumSupportBounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:39:47.166176+00:00
-- url     : https://prove2.me/theorems/2c1a2cfc-e60a-445a-b568-e30bb598c0e4
-- title:
--   Support bounds for the infimum of bounded rewards
-- statement:
--   The infimum of a countable family of measurable bounded rewards is measurable and lies between zero and the indicator of its positive event. Integrate the bounds.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.positiveRewardInfimumSupportBounds
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (g n))
    (h0 : ∀ n w, 0 ≤ g n w) (h1 : ∀ n w, g n w ≤ 1)
    (B : Set Ω) (hB : ∀ w, w ∈ B ↔ 0 < ⨅ n, g n w) :
    MeasurableSet B ∧
      (∫ w, ⨅ n, g n w ∂P) ≤ (P B).toReal ∧
      (P B = 0 → (∫ w, ⨅ n, g n w ∂P) = 0) := by
  sorry
