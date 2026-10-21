-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_eventually_polynomial_upper_core
-- name    : OAI.PiExponent.DeterminantContradiction.actualRowCount_eventually_polynomial_upper_core
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T23:27:35.917191+00:00
-- url     : https://prove2.me/theorems/09a4f88e-9472-4335-87ee-cf3b3281d2ee
-- title:
--   Eventual polynomial bound for actual row count, without a positivity condition on the constant
-- statement:
--   For fixed admissible data, the actual row count is eventually bounded by a real constant times `(H + 1)^(d.m + 1)`. This isolates the finite weighted-simplex counting estimate; no positivity condition is imposed on the constant.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped Topology

theorem OAI.PiExponent.DeterminantContradiction.actualRowCount_eventually_polynomial_upper_core
    {nu : ℝ} (d : FixedData nu) :
    ∃ C : ℝ,
      (∀ᶠ H : ℝ in atTop,
        (actualRowCount d H : ℝ) ≤ C * (H + 1) ^ (d.m + 1)) := by sorry
