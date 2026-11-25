-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_mem_range_ideleNorm_iff_forall
-- name    : GroundTheory.Global.IdeleNorm.mem_range_ideleNorm_iff_forall
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:04.856915+00:00
-- url     : https://prove2.me/theorems/15e5f1e8-4e76-4347-9375-b6078658b88e
-- title:
--   Idele Norm: mem range idele Norm iff forall
-- statement:
--   The Idele Norm construction uses the mem range idele Norm iff forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormsEverywhere.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNormsEverywhere.lean#L58-L67

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
variable (L)

theorem GroundTheory.Global.IdeleNorm.mem_range_ideleNorm_iff_forall (x : IdeleGroup K) :
    x ∈ (ideleNorm K L).range ↔
      (∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range) ∧
      ∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range := by sorry
