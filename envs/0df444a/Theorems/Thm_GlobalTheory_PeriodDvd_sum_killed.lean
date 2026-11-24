-- Prove2me | Theorems.Thm_GlobalTheory_PeriodDvd_sum_killed
-- name    : GlobalTheory.PeriodDvd.sum_killed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:42:28.085666+00:00
-- url     : https://prove2.me/theorems/2c52790c-1564-448f-b272-10c8c9c7accc
-- title:
--   Period Dvd: sum killed
-- statement:
--   The Period Dvd construction uses the sum killed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L64-L68

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

theorem GlobalTheory.PeriodDvd.sum_killed {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) (q : ℕ) :
    ∑ x ∈ killed d s, q ^ x.val = ∑ j ∈ Finset.range s, (q ^ e) ^ j := by sorry
