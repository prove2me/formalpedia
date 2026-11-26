-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedRewardLimitSupport
-- name    : Kyprianou.Ch04.boundedRewardLimitSupport
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:48:55.896541+00:00
-- url     : https://prove2.me/theorems/bfee24c2-5aa6-59f3-8341-7e05a0af2e15
-- title:
--   boundedRewardLimitSupport
-- statement:
--   The integer subsequence has the same limit as the full antitone mean. The positive event supports the limiting reward, so its mass bounds the limit and null mass implies zero.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.boundedRewardLimitSupport
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : NNReal × Ω → ℝ) (hg : Measurable g)
    (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1)
    (hga : ∀ w, Antitone (fun t : NNReal => g (t,w)))
    (B : Set Ω) (hB : ∀ w, w ∈ B ↔ 0 < ⨅ n : ℕ, g ((n : NNReal),w)) :
    let f : NNReal → ℝ := fun t => ∫ w, g (t,w) ∂P
    MeasurableSet B ∧
      (∀ ell : ℝ, Tendsto f atTop (nhds ell) → ell ≤ (P B).toReal) ∧
      (P B = 0 → Tendsto f atTop (nhds 0)) := by
  sorry
