-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_irreducible_pow_associated_le_card_of_span
-- name    : GlobalTheory.T.exists_irreducible_pow_associated_le_card_of_span
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:36:56.158802+00:00
-- url     : https://prove2.me/theorems/d777df8c-5a79-4bfa-9e81-b8e3308911c0
-- title:
--   T: exists irreducible pow associated le card of span
-- statement:
--   The T construction uses the exists irreducible pow associated le card of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RamificationLeCardOfSpanStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RamificationLeCardOfSpanStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationLeCardOfSpan
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationLeCardOfSpanStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_irreducible_pow_associated_le_card_of_span : ∀ (F : Type) [Field F] (T' T'' : Subring F), IsDiscreteValuationRing T' → IsDiscreteValuationRing T'' → ∀ (h : T' ≤ T''), (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) → ∀ (s : Finset F), (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) → ∀ π : T', Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ ∃ e : ℕ, 1 ≤ e ∧ e ≤ s.card ∧ Associated (Subring.inclusion h π) (ϖ ^ e) := by sorry
