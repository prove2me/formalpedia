-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_local_bounds_choice_order
-- name    : OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_choice_order
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T04:15:29.722824+00:00
-- url     : https://prove2.me/theorems/74160507-e69a-460f-ad77-63267693bb48
-- title:
--   Translation choice order bound
-- statement:
--   Show that the selected scalar order is at most `H / v0`, using the choice’s `Fin` membership and the row’s strict weighted-simplex budget.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_choice_order
    {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) :
    (t.2.2 : ℝ) ≤ H / (d.v0 : ℝ) := by sorry
