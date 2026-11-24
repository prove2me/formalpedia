-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_norm_sub_le_max_of_ultrametric_field
-- name    : GlobalTheory.CompanionTheory.RgFl.MaxLat.norm_sub_le_max_of_ultrametric_field
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:28.051233+00:00
-- url     : https://prove2.me/theorems/dcd410cc-12fe-4088-9289-5dfc8210a94c
-- title:
--   Max Lat: norm sub le max of ultrametric field
-- statement:
--   The Max Lat construction uses the norm sub le max of ultrametric field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistenceOfSandwichStatement.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistenceOfSandwichStatement.lean#L32-L33

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistenceOfSandwichStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl GlobalTheory.CompanionTheory.RgFl.MaxLat
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V]

theorem GlobalTheory.CompanionTheory.RgFl.MaxLat.norm_sub_le_max_of_ultrametric_field (a b : L) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by sorry
