-- Prove2me | Theorems.Thm_GlobalTheory_DualFrameSpan_eq_zero_of_trace_adjoint_comp_self
-- name    : GlobalTheory.DualFrameSpan.eq_zero_of_trace_adjoint_comp_self
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:51:46.906822+00:00
-- url     : https://prove2.me/theorems/aa218ebf-1a7d-4218-a82f-ccda05386948
-- title:
--   Dual Frame Span: eq zero of trace adjoint comp self
-- statement:
--   The Dual Frame Span construction uses the eq zero of trace adjoint comp self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualFrameSpanUnitaryRepresentation.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualFrameSpanUnitaryRepresentation.lean#L17-L32

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

theorem GlobalTheory.DualFrameSpan.eq_zero_of_trace_adjoint_comp_self (B : H →ₗ[ℂ] H)
    (h : LinearMap.trace ℂ H (LinearMap.adjoint B ∘ₗ B) = 0) : B = 0 := by sorry
