-- Prove2me | Theorems.Thm_GlobalTheory_DualFrameSpan_comp_mem_span
-- name    : GlobalTheory.DualFrameSpan.comp_mem_span
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:51:26.628844+00:00
-- url     : https://prove2.me/theorems/35d426fb-e9b8-4e82-9cfe-34bc00720ac8
-- title:
--   Dual Frame Span: comp mem span
-- statement:
--   The Dual Frame Span construction uses the comp mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualFrameSpanUnitaryRepresentation.lean#L69-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualFrameSpanUnitaryRepresentation.lean#L69-L79

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

theorem GlobalTheory.DualFrameSpan.comp_mem_span (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h) {h : G} (hh : h ∈ K)
    {X : H →ₗ[ℂ] H} (hX : X ∈ Submodule.span ℂ (ρ '' K)) :
    X ∘ₗ ρ h ∈ Submodule.span ℂ (ρ '' K) := by sorry
