-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_finiteProj_ideleNorm
-- name    : GroundTheory.Global.IdeleNorm.finiteProj_ideleNorm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:52:45.496625+00:00
-- url     : https://prove2.me/theorems/8f7e2969-819e-4cfb-b04a-76024cb6a687
-- title:
--   Idele Norm: finite Proj idele Norm
-- statement:
--   The Idele Norm construction uses the finite Proj idele Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L68-L73

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

theorem GroundTheory.Global.IdeleNorm.finiteProj_ideleNorm (y : IdeleGroup L) (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup.finiteProj v (ideleNorm K L y) =
      finiteLocalNorm L v (fun w ↦ IdeleGroup.finiteProj w.1 y) := by sorry
