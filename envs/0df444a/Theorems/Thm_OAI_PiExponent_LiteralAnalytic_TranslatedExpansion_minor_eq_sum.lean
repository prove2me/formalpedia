-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_minor_eq_sum
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.minor_eq_sum
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T02:57:41.674532+00:00
-- url     : https://prove2.me/theorems/b8bbe9d9-365a-437b-8485-5aaa8960a6bd
-- title:
--   Canonical translated determinant expansion of the actual minor
-- statement:
--   For positive H, the actual minor determinant equals the sum of the canonical translated scalar-product times period-matrix determinant over all rowwise choice families.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.minor_eq_sum
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) :
    (actualMinor d H selection).det = ∑ f : ChoiceFamily d H, summand d selection f := by sorry
