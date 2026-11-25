-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_selfAdjointTorus
-- name    : GroundTheory.Automorphic.HermitianForm.mem_selfAdjointTorus
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:58:11.939803+00:00
-- url     : https://prove2.me/theorems/e8549eef-71ba-5452-9062-eafebc541504
-- title:
--   Hermitian Form: mem self Adjoint Torus
-- statement:
--   The Hermitian Form construction uses the mem self Adjoint Torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L80-L81

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

theorem GroundTheory.Automorphic.HermitianForm.mem_selfAdjointTorus {c : TorusE (γ : V ≃ₗ[E] V)} :
    c ∈ h.selfAdjointTorus γ ↔ h.torusStar γ c = c := by sorry
