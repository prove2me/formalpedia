-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_stableInv_eq_stableInv_iff
-- name    : GroundTheory.Automorphic.HermitianForm.stableInv_eq_stableInv_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:13.266145+00:00
-- url     : https://prove2.me/theorems/ab45e834-aa3d-5a12-a0f8-7e7ce07915d3
-- title:
--   Hermitian Form: stable Inv eq stable Inv iff
-- statement:
--   The Hermitian Form construction uses the stable Inv eq stable Inv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L171-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L171-L205

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
open GroundTheory.Automorphic.HermitianForm
variable (h : HermitianForm F E V)
variable (γ : h.unitaryGroup) [Fact (IsRegularSemisimple (γ : V ≃ₗ[E] V))]

theorem GroundTheory.Automorphic.HermitianForm.stableInv_eq_stableInv_iff {γ₁ γ₂ : V ≃ₗ[E] V} (h₁ : γ₁ ∈ h.unitaryGroup)
    (h₂ : γ₂ ∈ h.unitaryGroup) (s₁ : StablyConjugate (γ : V ≃ₗ[E] V) γ₁)
    (s₂ : StablyConjugate (γ : V ≃ₗ[E] V) γ₂) :
    h.stableInv γ γ₁ = h.stableInv γ γ₂ ↔ ∃ u ∈ h.unitaryGroup, u * γ₁ * u⁻¹ = γ₂ := by sorry
