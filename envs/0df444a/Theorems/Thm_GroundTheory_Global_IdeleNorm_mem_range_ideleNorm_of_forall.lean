-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_mem_range_ideleNorm_of_forall
-- name    : GroundTheory.Global.IdeleNorm.mem_range_ideleNorm_of_forall
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:56:59.971403+00:00
-- url     : https://prove2.me/theorems/6a629dd4-79cf-5400-88d1-a02a2368d891
-- title:
--   Idele Norm: mem range idele Norm of forall
-- statement:
--   The Idele Norm construction uses the mem range idele Norm of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormsEverywhere.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormsEverywhere.lean#L69-L73

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormsEverywhere
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
open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem GroundTheory.Global.IdeleNorm.mem_range_ideleNorm_of_forall (x : IdeleGroup K)
    (hfin : ∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range)
    (hinf : ∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range) :
    x ∈ (ideleNorm K L).range := by sorry
