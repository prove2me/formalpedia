-- Prove2me | Theorems.Thm_GlobalTheory_ramification_le_card_of_span
-- name    : GlobalTheory.ramification_le_card_of_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:14:56.748998+00:00
-- url     : https://prove2.me/theorems/8cb02af4-96b6-4686-a520-833e44d4d113
-- title:
--   Global Theory: ramification le card of span
-- statement:
--   The Global Theory construction uses the ramification le card of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RamificationLeCardOfSpan.lean#L45-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RamificationLeCardOfSpan.lean#L45-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationLeCardOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.ramification_le_card_of_span :
    ∀ (F : Type) [Field F] (T' T'' : Subring F), IsDiscreteValuationRing T' →
      IsDiscreteValuationRing T'' → ∀ (h : T' ≤ T''),
      (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) → ∀ (s : Finset F),
      (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) →
      ∀ π : T', Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ ∃ e : ℕ, 1 ≤ e ∧ e ≤ s.card ∧
        Associated (Subring.inclusion h π) (ϖ ^ e) := by sorry
