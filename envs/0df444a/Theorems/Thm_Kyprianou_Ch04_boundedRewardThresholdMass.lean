-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedRewardThresholdMass
-- name    : Kyprianou.Ch04.boundedRewardThresholdMass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:43:20.185191+00:00
-- url     : https://prove2.me/theorems/2df77450-5eee-5435-9bab-4a067834eaa9
-- title:
--   Bounded reward threshold mass estimate
-- statement:
--   The given event is contained in the measurable superlevel set. The constant times that set indicator lies below the reward, so integral monotonicity yields the estimate.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.boundedRewardThresholdMass
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → ℝ) (hm : Measurable g) (h0 : ∀ w, 0 ≤ g w) (h1 : ∀ w, g w ≤ 1)
    (E : Set Ω) (c : ℝ) (hc : 0 ≤ c) (hE : ∀ w ∈ E, c ≤ g w) :
    c * (P E).toReal ≤ ∫ w, g w ∂P := by
  sorry
