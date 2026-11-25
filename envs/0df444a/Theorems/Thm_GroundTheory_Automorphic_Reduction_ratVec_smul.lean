-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_ratVec_smul
-- name    : GroundTheory.Automorphic.Reduction.ratVec_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:06:30.889275+00:00
-- url     : https://prove2.me/theorems/728a3f41-cd43-4639-8506-cf77c6c40cb3
-- title:
--   Reduction: rat Vec smul
-- statement:
--   The Reduction construction uses the rat Vec smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L196-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L196-L199

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.ratVec_smul (c : K) (x : Fin n → K) :
    ratVec (c • x) = algebraMap K 𝔸[K] c • ratVec x := by sorry
