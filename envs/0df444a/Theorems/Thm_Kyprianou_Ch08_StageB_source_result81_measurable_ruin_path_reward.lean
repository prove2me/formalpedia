-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_measurable_ruin_path_reward
-- name    : Kyprianou.Ch08.StageB.source_result81_measurable_ruin_path_reward
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:44:14.463885+00:00
-- url     : https://prove2.me/theorems/dc6b99ef-9dde-4418-8812-e17bdc341495
-- title:
--   Measurable discounted ruin payoff on right-continuous paths
-- statement:
--   A measurable path-space reward agrees on every right-continuous path with discounting its strict first lower passage from reserve a. The clock is the infimum of the positive rational witnesses, and nonnegative discount gives values between zero and one.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, strict ruin and stopped Markov argument. Analytic obligation of parent theorem 78574f78-b2c0-43ff-a7df-919c061143b7.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_measurable_ruin_path_reward (q a : ℝ) (hq : 0 ≤ q) :
    Measurable (fun t : ℝ≥0∞ => discountedAt q t) ∧
    (∀ t : ℝ≥0∞, 0 ≤ discountedAt q t ∧ discountedAt q t ≤ 1) ∧
    ∃ reward : (ℝ≥0 → ℝ) → ℝ,
      Measurable reward ∧
      ∀ f : ℝ≥0 → ℝ, (∀ t, ContinuousWithinAt f (Ici t) t) →
        reward f = discountedAt q (tauMinus (fun s (_ : Unit) => a + f s) 0 ()) := by
  sorry
