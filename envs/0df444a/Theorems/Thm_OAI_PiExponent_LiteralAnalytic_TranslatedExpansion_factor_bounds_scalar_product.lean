-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_factor_bounds_scalar_product
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_scalar_product
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T09:44:30.684442+00:00
-- url     : https://prove2.me/theorems/7631f389-4d14-40c3-b636-c841d01a0bf4
-- title:
--   Exponential bound for the translated scalar product
-- statement:
--   For nonnegative exponent parameter and positive height, the norm of the product of chosen scalars satisfies the stated exponential estimate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_scalar_product
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ} (hH : 0 < H)
    (f : ChoiceFamily d H) :
    ‖∏ r : Row d H, choiceScalar d r (f r)‖ ≤
      Real.exp (-nu * ((∑ r : Row d H, translatedIndexWeight d (f r).1) -
        (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * d.translationError) := by sorry
