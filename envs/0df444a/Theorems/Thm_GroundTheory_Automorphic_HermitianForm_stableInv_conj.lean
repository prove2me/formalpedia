-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_stableInv_conj
-- name    : GroundTheory.Automorphic.HermitianForm.stableInv_conj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:56:13.315013+00:00
-- url     : https://prove2.me/theorems/7943414c-3060-4d9c-b932-405fd4773866
-- title:
--   Hermitian Form: stable Inv conj
-- statement:
--   The Hermitian Form construction uses the stable Inv conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L157-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L157-L162

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

theorem GroundTheory.Automorphic.HermitianForm.stableInv_conj (g : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup) :
    h.stableInv γ (g * γ * g⁻¹) = h.invOf γ g hg := by sorry
