-- Prove2me | Theorems.Thm_GlobalTheory_SpanSingleInlMembership_mem_span_single_inl_iff
-- name    : GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:18:34.920634+00:00
-- url     : https://prove2.me/theorems/eb76e867-f4ab-4246-b200-78ccc5809f11
-- title:
--   Span Single Inl Membership: mem span single inl iff
-- statement:
--   The Span Single Inl Membership construction uses the mem span single inl iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/MemSpanSingleInlIff.lean#L5-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/MemSpanSingleInlIff.lean#L5-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_MemSpanSingleInlIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpanSingleInlMembership

theorem GlobalTheory.SpanSingleInlMembership.mem_span_single_inl_iff {g : ℕ} (S : Finset (Fin g)) (u : Fin g ⊕ Fin g → ℤ) :
    u ∈ Submodule.span ℤ ((fun (k : Fin g) ↦ Pi.single (Sum.inl k) (1 : ℤ)) '' (↑S : Set (Fin g))) ↔
      (∀ (k : Fin g), u (Sum.inr k) = (0 : ℤ)) ∧ ∀ k ∉ S, u (Sum.inl k) = (0 : ℤ) := by sorry
