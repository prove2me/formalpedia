-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_eventually_polynomial_upper
-- name    : OAI.PiExponent.DeterminantContradiction.actualRowCount_eventually_polynomial_upper
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T23:21:27.402135+00:00
-- url     : https://prove2.me/theorems/de75e639-8c64-4801-b695-9cc60937d2c6
-- title:
--   Polynomial upper bound for the actual row count
-- statement:
--   For each fixed admissible data set, the actual row count is eventually bounded by a positive constant times `(H + 1)^(d.m + 1)`. Each of the `d.m + 1` coordinates has a range of size bounded linearly in `H + 1`, since its fixed row weight is positive.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped Topology

theorem OAI.PiExponent.DeterminantContradiction.actualRowCount_eventually_polynomial_upper
    {nu : ℝ} (d : FixedData nu) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ H : ℝ in atTop,
        (actualRowCount d H : ℝ) ≤ C * (H + 1) ^ (d.m + 1)) := by sorry
