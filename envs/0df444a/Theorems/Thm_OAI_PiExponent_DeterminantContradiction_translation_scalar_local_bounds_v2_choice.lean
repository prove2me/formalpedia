-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_local_bounds_v2_choice
-- name    : OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_v2_choice
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:24:13.046096+00:00
-- url     : https://prove2.me/theorems/f6a23f53-dfcb-41bd-875c-d731d56a4dcc
-- title:
--   Translation choice order bound
-- statement:
--   Bound the selected scalar order using the `Fin` membership in the choice and the strict weighted-simplex budget of the row. Positivity of the first row weight and nonnegativity of the other weights make the strict budget imply the requested non-strict bound.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_v2_choice
    {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) :
    (t.2.2 : ℝ) ≤ H / (d.v0 : ℝ) := by sorry
