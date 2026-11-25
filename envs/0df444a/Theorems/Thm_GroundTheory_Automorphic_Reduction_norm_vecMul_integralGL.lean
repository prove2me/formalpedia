-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_vecMul_integralGL
-- name    : GroundTheory.Automorphic.Reduction.norm_vecMul_integralGL
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:11.192944+00:00
-- url     : https://prove2.me/theorems/391eee51-f6f2-43d7-8533-c714e848a7aa
-- title:
--   Reduction: norm vec Mul integral GL
-- statement:
--   The Reduction construction uses the norm vec Mul integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L171-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L171-L178

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
variable (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Automorphic.Reduction.norm_vecMul_integralGL {k : GL (Fin n) (v.adicCompletion K)}
    (hk : k ∈ GLnLocal.integralGL (v.adicCompletion K) n) (z : Fin n → v.adicCompletion K) :
    ‖z ᵥ* (k : Matrix (Fin n) (Fin n) (v.adicCompletion K))‖ = ‖z‖ := by sorry
