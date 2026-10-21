-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_actualMinor_entry_eq_choice_sum
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.actualMinor_entry_eq_choice_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T03:20:19.071767+00:00
-- url     : https://prove2.me/theorems/90e20d87-a8c3-444f-928d-8de2ed7eb151
-- title:
--   Entrywise translated expansion of the actual minor
-- statement:
--   Every selected matrix entry is the finite weighted sum of its translated row-choice contributions. Updating `f` at the selected row exposes the corresponding choice-matrix entry without changing the other rows.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.actualMinor_entry_eq_choice_sum
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H)
    (r c : Row d H) :
    actualMinor d H selection r c =
      ∑ t : RowChoice d H r,
        choiceScalar d r t *
          choiceMatrix d selection (Function.update f r t) r c := by sorry
