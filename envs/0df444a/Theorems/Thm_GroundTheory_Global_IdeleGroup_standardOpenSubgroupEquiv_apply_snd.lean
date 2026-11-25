-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
-- name    : GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:34.547649+00:00
-- url     : https://prove2.me/theorems/0061caa6-b47e-42fd-babb-0417d4d777d2
-- title:
--   Idele Group: standard Open Subgroup Equiv apply snd
-- statement:
--   The Idele Group construction uses the standard Open Subgroup Equiv apply snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/StandardOpenEquiv.lean#L155-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/StandardOpenEquiv.lean#L155-L158

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

theorem GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd (x : standardOpenSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    (standardOpenSubgroupEquiv K x).2 v = localIntegerUnit v x := by sorry

attribute [defeq] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
