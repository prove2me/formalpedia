-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_map_idealLevel_le_standardOpenSubgroup
-- name    : GroundTheory.Global.IdeleGroup.map_idealLevel_le_standardOpenSubgroup
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:28.11158+00:00
-- url     : https://prove2.me/theorems/485c03c5-676e-53cc-a8dd-f4eb728ec742
-- title:
--   Idele Group: map ideal Level le standard Open Subgroup
-- statement:
--   The Idele Group construction uses the map ideal Level le standard Open Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L167-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L167-L171

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup

theorem GroundTheory.Global.IdeleGroup.map_idealLevel_le_standardOpenSubgroup (𝔪 : Ideal (𝓞 K)) :
    (idealLevel 𝔪).map ofFinite ≤ standardOpenSubgroup K := by sorry
