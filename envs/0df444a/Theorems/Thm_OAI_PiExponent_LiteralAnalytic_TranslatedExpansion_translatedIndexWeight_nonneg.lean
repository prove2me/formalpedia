-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_translatedIndexWeight_nonneg
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.translatedIndexWeight_nonneg
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T10:03:25.982646+00:00
-- url     : https://prove2.me/theorems/c75f02cc-2543-4802-95d4-018aa532c965
-- title:
--   Nonnegativity of translated index weights
-- statement:
--   Each summand in a translated index weight is a product of nonnegative natural-number casts.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.translatedIndexWeight_nonneg {nu : ℝ} (d : FixedData nu) {H : ℝ} (a : indices d H) : 0 ≤ translatedIndexWeight d a := by sorry
