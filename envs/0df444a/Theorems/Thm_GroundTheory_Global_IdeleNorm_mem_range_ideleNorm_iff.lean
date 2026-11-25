-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_mem_range_ideleNorm_iff
-- name    : GroundTheory.Global.IdeleNorm.mem_range_ideleNorm_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:51:26.236641+00:00
-- url     : https://prove2.me/theorems/7f3e0c9a-9dff-45cb-84ab-edc0c1a7092a
-- title:
--   Idele Norm: mem range idele Norm iff
-- statement:
--   The Idele Norm construction uses the mem range idele Norm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L194-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L194-L205

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

theorem GroundTheory.Global.IdeleNorm.mem_range_ideleNorm_iff (x : IdeleGroup K) :
    x ∈ (ideleNorm K L).range ↔
      (∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range) ∧
      (∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range) ∧
      ∀ᶠ v in cofinite,
        IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v) := by sorry
