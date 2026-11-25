-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_adelicNorm_smul_rat
-- name    : GroundTheory.Automorphic.Reduction.adelicNorm_smul_rat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:09:18.055231+00:00
-- url     : https://prove2.me/theorems/abfb56f5-8dea-426f-8498-41a34822e356
-- title:
--   Reduction: adelic Norm smul rat
-- statement:
--   The Reduction construction uses the adelic Norm smul rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L251-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L251-L255

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

theorem GroundTheory.Automorphic.Reduction.adelicNorm_smul_rat {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y) {c : K} (hc : c ≠ 0) :
    adelicNorm (algebraMap K 𝔸[K] c • y) = adelicNorm y := by sorry
