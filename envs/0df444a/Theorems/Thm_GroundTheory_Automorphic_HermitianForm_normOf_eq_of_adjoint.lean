-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_normOf_eq_of_adjoint
-- name    : GroundTheory.Automorphic.HermitianForm.normOf_eq_of_adjoint
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:57:23.191224+00:00
-- url     : https://prove2.me/theorems/7373b01c-b934-5890-9131-91bfdbffbc6d
-- title:
--   Hermitian Form: norm Of eq of adjoint
-- statement:
--   The Hermitian Form construction uses the norm Of eq of adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L126-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L126-L129

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

theorem GroundTheory.Automorphic.HermitianForm.normOf_eq_of_adjoint (g g' : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup)
    (hg' : g' * γ * g'⁻¹ ∈ h.unitaryGroup)
    (hgg : h.adjointEquiv g * g = h.adjointEquiv g' * g') : h.normOf γ g hg = h.normOf γ g' hg' := by sorry
