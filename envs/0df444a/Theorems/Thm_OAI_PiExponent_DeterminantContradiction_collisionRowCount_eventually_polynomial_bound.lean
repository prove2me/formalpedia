-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_collisionRowCount_eventually_polynomial_bound
-- name    : OAI.PiExponent.DeterminantContradiction.collisionRowCount_eventually_polynomial_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T23:14:15.191416+00:00
-- url     : https://prove2.me/theorems/19f8f71f-07d9-4be7-88ef-e1583c208020
-- title:
--   Eventual polynomial bound for the collision row count
-- statement:
--   For each fixed admissible data set, the actual row count is eventually at least one and is bounded above by a constant times `(H + 1)^(d.m + 1)`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open scoped Topology

theorem OAI.PiExponent.DeterminantContradiction.collisionRowCount_eventually_polynomial_bound
    {nu : ℝ} (d : FixedData nu) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ H : ℝ in atTop, 1 ≤ (actualRowCount d H : ℝ)) ∧
      (∀ᶠ H : ℝ in atTop,
        (actualRowCount d H : ℝ) ≤ C * (H + 1) ^ (d.m + 1)) := by sorry
