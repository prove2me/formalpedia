-- Prove2me | Theorems.Thm_GlobalTheory_card_dvd_sum_of_invariant_of_card_stabilizer_dvd
-- name    : GlobalTheory.card_dvd_sum_of_invariant_of_card_stabilizer_dvd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:35.361436+00:00
-- url     : https://prove2.me/theorems/15b64395-ba43-49b0-aa98-22b5c8f1bb88
-- title:
--   Global Theory: card dvd sum of invariant of card stabilizer dvd
-- statement:
--   The Global Theory construction uses the card dvd sum of invariant of card stabilizer dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardDvdSumOfInvariantOfCardStabilizerDvd.lean#L5-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardDvdSumOfInvariantOfCardStabilizerDvd.lean#L5-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.card_dvd_sum_of_invariant_of_card_stabilizer_dvd (G X : Type) [AddGroup G] [Finite G]
    [Fintype X] [AddAction G X] (h : X → ℤ) (hinv : ∀ (g : G) (x : X), h (g +ᵥ x) = h x)
    (hdvd : ∀ x, (Nat.card (AddAction.stabilizer G x) : ℤ) ∣ h x) :
    (Nat.card G : ℤ) ∣ ∑ x, h x := by sorry
