-- Prove2me | Theorems.Thm_GlobalTheory_DualFrameSpan_pairing_apply
-- name    : GlobalTheory.DualFrameSpan.pairing_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:46.168915+00:00
-- url     : https://prove2.me/theorems/9528547b-d62b-4194-840c-b7bf295813f1
-- title:
--   Dual Frame Span: pairing apply
-- statement:
--   The Dual Frame Span construction uses the pairing apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualFrameSpanUnitaryRepresentation.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualFrameSpanUnitaryRepresentation.lean#L39-L40

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

theorem GlobalTheory.DualFrameSpan.pairing_apply (W : Submodule ℂ (H →ₗ[ℂ] H)) (X Y : W) :
    pairing W X Y = LinearMap.trace ℂ H ((X : H →ₗ[ℂ] H) ∘ₗ (Y : H →ₗ[ℂ] H)) := by sorry
