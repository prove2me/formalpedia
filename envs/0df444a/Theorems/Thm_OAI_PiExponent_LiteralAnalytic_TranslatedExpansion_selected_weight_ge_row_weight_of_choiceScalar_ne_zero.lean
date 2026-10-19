-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_selected_weight_ge_row_weight_of_choiceScalar_ne_zero
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.selected_weight_ge_row_weight_of_choiceScalar_ne_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T13:07:56.609695+00:00
-- url     : https://prove2.me/theorems/4bfd03fb-c810-4e8f-af8d-ee44556ef770
-- title:
--   A nonzero row choice has sufficient translated weight
-- statement:
--   For a row whose chosen scalar is nonzero, the selected translated index has weighted degree at least the row's weighted degree.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.selected_weight_ge_row_weight_of_choiceScalar_ne_zero
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (f : ChoiceFamily d H) (r : Row d H)
    (hr : choiceScalar d r (f r) ≠ 0) :
    (∑ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i *
        (r.2.1 i.succ : ℝ)) ≤
      translatedIndexWeight d (f r).1 := by sorry
