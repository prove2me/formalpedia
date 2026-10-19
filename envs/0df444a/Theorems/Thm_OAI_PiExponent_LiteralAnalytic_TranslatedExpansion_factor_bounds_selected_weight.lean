-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_factor_bounds_selected_weight
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_selected_weight
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T09:44:00.721782+00:00
-- url     : https://prove2.me/theorems/08926992-c070-45e3-b223-e6877ea401a6
-- title:
--   Nonzero choices force a lower bound on total selected weight
-- statement:
--   If all chosen scalar factors have nonzero product, the total selected translated weight is at least the row-count times height times the actual mean.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_selected_weight
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (f : ChoiceFamily d H)
    (hs : (∏ r : Row d H, choiceScalar d r (f r)) ≠ 0) :
    (actualRowCount d H : ℝ) * H * actualMean d H ≤
      ∑ r : Row d H, translatedIndexWeight d (f r).1 := by sorry
