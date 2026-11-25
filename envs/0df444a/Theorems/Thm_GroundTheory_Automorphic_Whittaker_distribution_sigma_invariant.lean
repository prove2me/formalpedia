-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_distribution_sigma_invariant
-- name    : GroundTheory.Automorphic.Whittaker.distribution_sigma_invariant
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:40:48.525724+00:00
-- url     : https://prove2.me/theorems/b2f52267-8568-4ec5-aaa9-de6578973b0a
-- title:
--   Whittaker: distribution sigma invariant
-- statement:
--   The Whittaker construction uses the distribution sigma invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L709-L748
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L709-L748

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

theorem GroundTheory.Automorphic.Whittaker.distribution_sigma_invariant (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1)
    (D : Module.Dual ℂ (locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ))
    (hD : ∀ (f : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) (u₁ u₂ : GL (Fin n) F)
      (_ : u₁ ∈ Iwasawa.unipotent F n) (_ : u₂ ∈ Iwasawa.unipotent F n),
      D ⟨fun x => (f : GL (Fin n) F → ℂ) (u₁⁻¹ * x * u₂), twoSided_mem f.2 u₁ u₂⟩ =
        psiN ψ₀ u₁ * (psiN ψ₀ u₂)⁻¹ * D f)
    (f : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) :
    D ⟨fun x => (f : GL (Fin n) F → ℂ) (sigma x), comp_sigma_mem f.2⟩ = D f := by sorry
