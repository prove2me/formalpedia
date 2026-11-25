-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_inKernel_mk
-- name    : GroundTheory.Automorphic.HermitianForm.inKernel_mk
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:58:10.195302+00:00
-- url     : https://prove2.me/theorems/9c630dae-5ec9-5ffd-837d-0445a8846764
-- title:
--   Hermitian Form: in Kernel mk
-- statement:
--   The Hermitian Form construction uses the in Kernel mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L232-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L232-L233

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

theorem GroundTheory.Automorphic.HermitianForm.inKernel_mk (c : h.selfAdjointTorus γ) :
    h.InKernel γ (QuotientGroup.mk c) ↔ Isometric (h.twistOf γ c) h := by sorry
