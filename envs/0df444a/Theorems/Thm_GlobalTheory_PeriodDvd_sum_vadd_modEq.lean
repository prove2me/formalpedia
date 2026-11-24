-- Prove2me | Theorems.Thm_GlobalTheory_PeriodDvd_sum_vadd_modEq
-- name    : GlobalTheory.PeriodDvd.sum_vadd_modEq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:42:14.768837+00:00
-- url     : https://prove2.me/theorems/5603e867-89ec-46ef-9780-3d47e5f2a1ae
-- title:
--   Period Dvd: sum vadd mod Eq
-- statement:
--   The Period Dvd construction uses the sum vadd mod Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L97-L103

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

theorem GlobalTheory.PeriodDvd.sum_vadd_modEq {d : ℕ} [NeZero d] (q : ℕ) (hq : 1 ≤ q) (g : ZMod d) (I : Finset (ZMod d)) :
    (∑ x ∈ I, q ^ x.val) * q ^ g.val ≡ ∑ x ∈ g +ᵥ I, q ^ x.val [MOD q ^ d - 1] := by sorry
