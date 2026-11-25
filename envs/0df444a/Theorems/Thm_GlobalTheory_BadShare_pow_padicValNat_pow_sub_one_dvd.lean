-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_pow_padicValNat_pow_sub_one_dvd
-- name    : GlobalTheory.BadShare.pow_padicValNat_pow_sub_one_dvd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:06.277751+00:00
-- url     : https://prove2.me/theorems/3f907823-6b1f-42d5-8f7e-f6b7ac888e3c
-- title:
--   Bad Share: pow padic Val Nat pow sub one dvd
-- statement:
--   The Bad Share construction uses the pow padic Val Nat pow sub one dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumPrimePowerPartPowSubOneLe.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumPrimePowerPartPowSubOneLe.lean#L80-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumPrimePowerPartPowSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare

theorem GlobalTheory.BadShare.pow_padicValNat_pow_sub_one_dvd (g d l : ℕ) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hd : d ≠ 0)
    (hl : l.Prime) (hlg : l ∣ g - 1) : l ^ padicValNat l (g ^ d - 1) ∣ d * (g - 1) := by sorry
