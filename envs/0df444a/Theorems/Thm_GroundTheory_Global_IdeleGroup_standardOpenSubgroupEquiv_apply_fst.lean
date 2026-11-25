-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
-- name    : GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:57.740559+00:00
-- url     : https://prove2.me/theorems/f450f345-f452-4fe0-9106-ecc33cd3d5da
-- title:
--   Idele Group: standard Open Subgroup Equiv apply fst
-- statement:
--   The Idele Group construction uses the standard Open Subgroup Equiv apply fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/StandardOpenEquiv.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/StandardOpenEquiv.lean#L150-L152

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst (x : standardOpenSubgroup K) :
    (standardOpenSubgroupEquiv K x).1 = toInfinite K (x : IdeleGroup K) := by sorry

attribute [defeq] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
