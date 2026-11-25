-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_stableInv_eq_iff
-- name    : GroundTheory.Automorphic.HermitianForm.exists_stableInv_eq_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:34.116981+00:00
-- url     : https://prove2.me/theorems/f6a97ecb-3521-47de-b7a5-27c2a37e0f9e
-- title:
--   Hermitian Form: exists stable Inv eq iff
-- statement:
--   The Hermitian Form construction uses the exists stable Inv eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L235-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L235-L256

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

theorem GroundTheory.Automorphic.HermitianForm.exists_stableInv_eq_iff (x : h.centralizerTorusFirstCohomology γ) :
    (∃ γ' ∈ h.unitaryGroup, StablyConjugate (γ : V ≃ₗ[E] V) γ' ∧ h.stableInv γ γ' = x) ↔
      h.InKernel γ x := by sorry
