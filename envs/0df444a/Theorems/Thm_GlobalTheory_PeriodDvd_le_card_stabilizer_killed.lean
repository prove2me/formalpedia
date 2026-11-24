-- Prove2me | Theorems.Thm_GlobalTheory_PeriodDvd_le_card_stabilizer_killed
-- name    : GlobalTheory.PeriodDvd.le_card_stabilizer_killed
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:42:11.120985+00:00
-- url     : https://prove2.me/theorems/c05de90e-db1f-440b-911b-06300bf70d51
-- title:
--   Period Dvd: le card stabilizer killed
-- statement:
--   The Period Dvd construction uses the le card stabilizer killed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L119-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L119-L135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open GlobalTheory.PeriodDvd

theorem GlobalTheory.PeriodDvd.le_card_stabilizer_killed {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) :
    s ∣ Nat.card (AddAction.stabilizer (ZMod d) (killed d s)) := by sorry
