-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_rayGroup_le
-- name    : GroundTheory.Global.IdeleGroup.rayGroup_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:12:47.282769+00:00
-- url     : https://prove2.me/theorems/3675611a-af6a-41ea-a974-8df5f20fbcb8
-- title:
--   Idele Group: ray Group le
-- statement:
--   The Idele Group construction uses the ray Group le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L179-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L179-L182

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

theorem GroundTheory.Global.IdeleGroup.rayGroup_le (𝔪 : Ideal (𝓞 K)) :
    rayGroup K 𝔪 ≤ (diagonal K).range ⊔ standardOpenSubgroup K := by sorry
