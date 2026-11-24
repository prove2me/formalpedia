-- Prove2me | Theorems.Thm_GlobalTheory_card_pow_eq_one_two_pow_le
-- name    : GlobalTheory.card_pow_eq_one_two_pow_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:07:45.499532+00:00
-- url     : https://prove2.me/theorems/bd84beaf-f966-4aee-8bec-24b8b4f50e04
-- title:
--   Global Theory: card pow eq one two pow le
-- statement:
--   The Global Theory construction uses the card pow eq one two pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPowEqOneLeOfIsCyclicUnits.lean#L52-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPowEqOneLeOfIsCyclicUnits.lean#L52-L76

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPowEqOneLeOfIsCyclicUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.card_pow_eq_one_two_pow_le (w : ℕ) (hw : 1 ≤ w) {d : ℕ} (hd : 0 < d) :
    Nat.card {x : ZMod (2 ^ w) // x ^ d = 1} ≤ 2 * d := by sorry
