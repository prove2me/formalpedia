-- Prove2me | Theorems.Thm_GlobalTheory_PeriodDvd_sum_finset_zmod
-- name    : GlobalTheory.PeriodDvd.sum_finset_zmod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:42:12.605935+00:00
-- url     : https://prove2.me/theorems/6da5e796-b2f4-4038-a115-ea38e87ce844
-- title:
--   Period Dvd: sum finset zmod
-- statement:
--   The Period Dvd construction uses the sum finset zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L137-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L137-L161

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

theorem GlobalTheory.PeriodDvd.sum_finset_zmod {d : ℕ} [NeZero d] (s : ℕ) (f : ℕ → ℤ) (q : ℕ) :
    ∑ I : Finset (ZMod d), (if I.card = s then f (∑ x ∈ I, q ^ x.val) else 0)
      = ∑ I ∈ (Finset.range d).powersetCard s, f (∑ i ∈ I, q ^ i) := by sorry
