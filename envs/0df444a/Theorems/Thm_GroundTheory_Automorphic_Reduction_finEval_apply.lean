-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_finEval_apply
-- name    : GroundTheory.Automorphic.Reduction.finEval_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:07:46.555808+00:00
-- url     : https://prove2.me/theorems/a032c5a1-38cf-417d-8a04-b1d446f65efb
-- title:
--   Reduction: fin Eval apply
-- statement:
--   The Reduction construction uses the fin Eval apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L86-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L86-L86

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

theorem GroundTheory.Automorphic.Reduction.finEval_apply (v : HeightOneSpectrum (𝓞 K)) (a : 𝔸[K]) : finEval v a = a.2 v := by sorry

attribute [defeq] GroundTheory.Automorphic.Reduction.finEval_apply
