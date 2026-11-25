-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_ratVec_vecMul
-- name    : GroundTheory.Automorphic.Reduction.ratVec_vecMul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:11.830708+00:00
-- url     : https://prove2.me/theorems/af571444-0091-49bb-8ded-8925507ba252
-- title:
--   Reduction: rat Vec vec Mul
-- statement:
--   The Reduction construction uses the rat Vec vec Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L201-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L201-L204

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

theorem GroundTheory.Automorphic.Reduction.ratVec_vecMul (x : Fin n → K) (M : Matrix (Fin n) (Fin n) K) :
    ratVec (x ᵥ* M) = ratVec x ᵥ* M.map (algebraMap K 𝔸[K]) := by sorry
