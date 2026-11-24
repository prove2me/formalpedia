-- Prove2me | Theorems.Thm_GlobalTheory_DualFrameSpan_adjoint_mem_span
-- name    : GlobalTheory.DualFrameSpan.adjoint_mem_span
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:51:33.741371+00:00
-- url     : https://prove2.me/theorems/f6caf83d-c367-4440-8975-7e5c942686b8
-- title:
--   Dual Frame Span: adjoint mem span
-- statement:
--   The Dual Frame Span construction uses the adjoint mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualFrameSpanUnitaryRepresentation.lean#L57-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualFrameSpanUnitaryRepresentation.lean#L57-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualFrameSpanUnitaryRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.DualFrameSpan
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {G : Type} [Mul G] (K : Set G) (ρ : G → (H →ₗ[ℂ] H))

theorem GlobalTheory.DualFrameSpan.adjoint_mem_span (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g')
    {X : H →ₗ[ℂ] H} (hX : X ∈ Submodule.span ℂ (ρ '' K)) :
    LinearMap.adjoint X ∈ Submodule.span ℂ (ρ '' K) := by sorry
