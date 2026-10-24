-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualMinor_entry_translation_expansion
-- name    : OAI.PiExponent.DeterminantContradiction.actualMinor_entry_translation_expansion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T04:10:43.356909+00:00
-- url     : https://prove2.me/theorems/4d988bef-3bab-4fba-88d3-69c52a365b14
-- title:
--   Selected minor entries expand over row translations
-- statement:
--   Each selected entry is the finite sum over the row’s translation choices, with the staged scalar weight and the corresponding coefficient of the translated period monomial. The default family supplies the other rows when the chosen row entry is formed.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.actualMinor_entry_translation_expansion
    {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) (f0 : ChoiceFamily d H)
    (r c : Row d H) :
    (actualMinor d H selection) r c =
      ∑ t : RowChoice d H r,
        choiceScalar d r t *
          (choiceMatrix d selection (Function.update f0 r t)) r c := by sorry
