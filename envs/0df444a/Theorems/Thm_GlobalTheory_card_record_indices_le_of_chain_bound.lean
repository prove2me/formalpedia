-- Prove2me | Theorems.Thm_GlobalTheory_card_record_indices_le_of_chain_bound
-- name    : GlobalTheory.card_record_indices_le_of_chain_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:33.271903+00:00
-- url     : https://prove2.me/theorems/16f38a6c-9592-4c57-a4fb-8166bf229e3b
-- title:
--   Global Theory: card record indices le of chain bound
-- statement:
--   The Global Theory construction uses the card record indices le of chain bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ChainLengthBoundOfSupInf.lean#L5-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ChainLengthBoundOfSupInf.lean#L5-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ChainLengthBoundOfSupInf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.card_record_indices_le_of_chain_bound {α : Type} [Preorder α] (Q : α → Prop) (L : ℕ)
    (h : ∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q (N i)) → r ≤ L)
    {r : ℕ} (a : Fin r → α) (ha : ∀ i, Q (a i)) (T : Finset (Fin r))
    (hT : ∀ j ∈ T, ∀ i < j, a i < a j) : T.card ≤ L := by sorry
