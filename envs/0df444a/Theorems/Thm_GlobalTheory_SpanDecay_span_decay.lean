-- Prove2me | Theorems.Thm_GlobalTheory_SpanDecay_span_decay
-- name    : GlobalTheory.SpanDecay.span_decay
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:18:29.913315+00:00
-- url     : https://prove2.me/theorems/22f5bafc-fa2e-4e85-a33c-0243f156b0cc
-- title:
--   Span Decay: span decay
-- statement:
--   The Span Decay construction uses the span decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanDecay.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanDecay.lean#L5-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpanDecay

theorem GlobalTheory.SpanDecay.span_decay : (let d1 : {G H : Type} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → (G → H →L[ℂ] H) → (G → ℝ) → ℝ → H → H → Prop := @(fun {G H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : G → H →L[ℂ] H) (D : G → ℝ) (c : ℝ) (v u : H) ↦ ∃ (C : ℝ), ∀ (g : G), ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g))); ∀ {G H : Type} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {ρ : G → H →L[ℂ] H} {D : G → ℝ} {c : ℝ} {S : Set H} {v : H}, (∀ u ∈ S, d1 ρ D c v u) → ∀ u ∈ Submodule.span ℂ S, d1 ρ D c v u) := by sorry
