-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_row_coordinate_le_index_of_choiceScalar_ne_zero
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.row_coordinate_le_index_of_choiceScalar_ne_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T21:32:27.11404+00:00
-- url     : https://prove2.me/theorems/b1a448b9-4099-4d9f-913e-2b87a4de9fbf
-- title:
--   Nonzero row choices dominate row coordinates
-- statement:
--   If the selected row choice has nonzero scalar, each row coordinate is at most the corresponding selected-index coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.row_coordinate_le_index_of_choiceScalar_ne_zero
    {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (f : ChoiceFamily d H) (r : Row d H)
    (hr : choiceScalar d r (f r) ≠ 0) :
    ∀ i : Fin d.m, r.2.1 i.succ ≤ (f r).1.1 i := by sorry
