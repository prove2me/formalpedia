-- Prove2me | Theorems.Thm_GlobalTheory_PeriodDvd_card_stabilizer_dvd
-- name    : GlobalTheory.PeriodDvd.card_stabilizer_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:23.001829+00:00
-- url     : https://prove2.me/theorems/ca6280aa-12b2-486d-9ca6-6f54d4f548d1
-- title:
--   Period Dvd: card stabilizer dvd
-- statement:
--   The Period Dvd construction uses the card stabilizer dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L114-L117

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

theorem GlobalTheory.PeriodDvd.card_stabilizer_dvd {d : ℕ} [NeZero d] (I : Finset (ZMod d)) :
    Nat.card (AddAction.stabilizer (ZMod d) I) ∣ d := by sorry
