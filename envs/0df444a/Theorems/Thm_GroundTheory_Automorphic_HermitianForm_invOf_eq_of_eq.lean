-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_invOf_eq_of_eq
-- name    : GroundTheory.Automorphic.HermitianForm.invOf_eq_of_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:56:09.252919+00:00
-- url     : https://prove2.me/theorems/7168055e-e659-4947-9318-94f45bbc47ef
-- title:
--   Hermitian Form: inv Of eq of eq
-- statement:
--   The Hermitian Form construction uses the inv Of eq of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L131-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L131-L150

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

theorem GroundTheory.Automorphic.HermitianForm.invOf_eq_of_eq (g g' : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup)
    (hg' : g' * γ * g'⁻¹ ∈ h.unitaryGroup) (heq : g * γ * g⁻¹ = g' * γ * g'⁻¹) :
    h.invOf γ g hg = h.invOf γ g' hg' := by sorry
