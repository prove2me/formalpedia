-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_actual_weight_sum_eq_row_count_height_mean
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.actual_weight_sum_eq_row_count_height_mean
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T13:08:26.934926+00:00
-- url     : https://prove2.me/theorems/ec47ea34-a9d4-4404-9cf1-e9e747f83e6f
-- title:
--   The actual mean recovers the total row weight
-- statement:
--   Multiplying the actual mean by the row count and height gives the sum of all row weights.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.actual_weight_sum_eq_row_count_height_mean
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (actualRowCount d H : ℝ) * H * actualMean d H =
      ∑ r : Row d H,
        ∑ i : Fin d.m,
          MatrixArithmetic.logWeights (finiteDenominators d) i *
            (r.2.1 i.succ : ℝ) := by sorry
