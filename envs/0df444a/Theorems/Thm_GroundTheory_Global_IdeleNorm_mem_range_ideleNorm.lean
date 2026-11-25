-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_mem_range_ideleNorm
-- name    : GroundTheory.Global.IdeleNorm.mem_range_ideleNorm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:31.298267+00:00
-- url     : https://prove2.me/theorems/fbcb372d-ab14-578d-91b4-d5efd7fb5cd7
-- title:
--   Idele Norm: mem range idele Norm
-- statement:
--   The Idele Norm construction uses the mem range idele Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L171-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L171-L192

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
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
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]
variable {L}

theorem GroundTheory.Global.IdeleNorm.mem_range_ideleNorm (x : IdeleGroup K)
    (hfin : ∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range)
    (hinf : ∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range)
    (hint : ∀ᶠ v in cofinite,
      IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v)) :
    x ∈ (ideleNorm K L).range := by sorry
