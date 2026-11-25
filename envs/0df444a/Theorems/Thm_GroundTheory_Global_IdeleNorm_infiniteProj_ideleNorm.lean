-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_infiniteProj_ideleNorm
-- name    : GroundTheory.Global.IdeleNorm.infiniteProj_ideleNorm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:42.274672+00:00
-- url     : https://prove2.me/theorems/9baa29e9-f5b0-5eaa-9ba9-a6868279e5fe
-- title:
--   Idele Norm: infinite Proj idele Norm
-- statement:
--   The Idele Norm construction uses the infinite Proj idele Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L75-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L75-L81

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

theorem GroundTheory.Global.IdeleNorm.infiniteProj_ideleNorm (y : IdeleGroup L) (v : InfinitePlace K) :
    IdeleGroup.infiniteProj v (ideleNorm K L y) =
      infiniteLocalNorm L v (fun w ↦ IdeleGroup.infiniteProj (w : InfinitePlace L) y) := by sorry
