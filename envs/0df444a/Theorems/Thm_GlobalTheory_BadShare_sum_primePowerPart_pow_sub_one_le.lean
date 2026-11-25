-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_sum_primePowerPart_pow_sub_one_le
-- name    : GlobalTheory.BadShare.sum_primePowerPart_pow_sub_one_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:20.764658+00:00
-- url     : https://prove2.me/theorems/02d09dea-115b-44f7-aa37-b87648c8e46d
-- title:
--   Bad Share: sum prime Power Part pow sub one le
-- statement:
--   The Bad Share construction uses the sum prime Power Part pow sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumPrimePowerPartPowSubOneLe.lean#L85-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumPrimePowerPartPowSubOneLe.lean#L85-L133

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

theorem GlobalTheory.BadShare.sum_primePowerPart_pow_sub_one_le :
    ∀ g d : ℕ, 2 ≤ g → 4 ∣ g - 1 → 2 ≤ d → (∑ l ∈ (g ^ d - 1).primeFactors, ((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ)) ≤ d * ((g : ℝ) - 1) + ((g : ℝ) ^ d - 1) / ((g : ℝ) - 1) := by sorry
