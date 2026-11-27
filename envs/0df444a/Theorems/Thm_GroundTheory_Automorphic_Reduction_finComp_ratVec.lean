-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_finComp_ratVec
-- name    : GroundTheory.Automorphic.Reduction.finComp_ratVec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:53:52.723814+00:00
-- url     : https://prove2.me/theorems/6c9bd3d7-802b-59c6-bbbb-0fc5d2af3cc6
-- title:
--   Reduction: fin Comp rat Vec
-- statement:
--   The Reduction construction uses the fin Comp rat Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L190-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L190-L191

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

theorem GroundTheory.Automorphic.Reduction.finComp_ratVec (v : HeightOneSpectrum (𝓞 K)) (x : Fin n → K) (i : Fin n) :
    finComp v (ratVec x) i = (x i : v.adicCompletion K) := by sorry
