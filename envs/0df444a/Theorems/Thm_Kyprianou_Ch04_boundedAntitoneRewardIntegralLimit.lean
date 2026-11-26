-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedAntitoneRewardIntegralLimit
-- name    : Kyprianou.Ch04.boundedAntitoneRewardIntegralLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:35:16.758799+00:00
-- url     : https://prove2.me/theorems/98c33b01-2c65-5d30-9197-be35aefe40f2
-- title:
--   Bounded antitone reward integral limit
-- statement:
--   Bounded decreasing real sequences converge to their infimum and dominated convergence transfers the limit to their integrals.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.boundedAntitoneRewardIntegralLimit
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (g n))
    (h0 : ∀ n w, 0 ≤ g n w) (h1 : ∀ n w, g n w ≤ 1)
    (ha : ∀ w, Antitone (fun n => g n w)) :
    Tendsto (fun n => ∫ w, g n w ∂P) atTop
      (nhds (∫ w, ⨅ n, g n w ∂P)) := by
  sorry
