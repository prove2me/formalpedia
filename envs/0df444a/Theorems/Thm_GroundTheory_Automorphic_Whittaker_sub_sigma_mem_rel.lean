-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_sub_sigma_mem_rel
-- name    : GroundTheory.Automorphic.Whittaker.sub_sigma_mem_rel
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:07:38.180657+00:00
-- url     : https://prove2.me/theorems/d50a54f7-8239-418e-a28d-363c742ad381
-- title:
--   Whittaker: sub sigma mem rel
-- statement:
--   The Whittaker construction uses the sub sigma mem rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L684-L689
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L684-L689

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
attribute [local instance] totallyDisconnectedSpace_localField
attribute [local instance] continuousSMul_biAction
variable (ψ₀ : AddChar F ℂ)

theorem GroundTheory.Automorphic.Whittaker.sub_sigma_mem_rel (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) {f : GL (Fin n) F → ℂ}
    (hf : f ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) :
    f - sigmaL f ∈ rel n ψ₀ := by sorry
