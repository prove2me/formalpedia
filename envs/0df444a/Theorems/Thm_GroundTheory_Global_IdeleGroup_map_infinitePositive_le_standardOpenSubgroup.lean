-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_map_infinitePositive_le_standardOpenSubgroup
-- name    : GroundTheory.Global.IdeleGroup.map_infinitePositive_le_standardOpenSubgroup
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:13:46.687965+00:00
-- url     : https://prove2.me/theorems/3e7915f6-8762-40b3-81a8-9a812d3af397
-- title:
--   Idele Group: map infinite Positive le standard Open Subgroup
-- statement:
--   The Idele Group construction uses the map infinite Positive le standard Open Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L173-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L173-L177

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

theorem GroundTheory.Global.IdeleGroup.map_infinitePositive_le_standardOpenSubgroup :
    (infinitePositive K).map ofInfinite ≤ standardOpenSubgroup K := by sorry
