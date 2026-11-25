-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_eventually_finiteProj_mem
-- name    : GroundTheory.Global.IdeleNorm.eventually_finiteProj_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:50:08.457136+00:00
-- url     : https://prove2.me/theorems/382ca412-5ee3-54f4-9d9d-ab84e9d2afc5
-- title:
--   Idele Norm: eventually finite Proj mem
-- statement:
--   The Idele Norm construction uses the eventually finite Proj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L83-L90

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

theorem GroundTheory.Global.IdeleNorm.eventually_finiteProj_mem (y : IdeleGroup L) :
    ∀ᶠ w in cofinite,
      IdeleGroup.finiteProj w y ∈ (Submonoid.ofClass (w.adicCompletionIntegers L)).units := by sorry
