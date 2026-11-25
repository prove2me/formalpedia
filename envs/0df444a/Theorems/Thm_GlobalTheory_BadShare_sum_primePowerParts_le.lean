-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_sum_primePowerParts_le
-- name    : GlobalTheory.BadShare.sum_primePowerParts_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:31.457935+00:00
-- url     : https://prove2.me/theorems/9fc62198-0242-4deb-b86d-ccb068d97344
-- title:
--   Bad Share: sum prime Power Parts le
-- statement:
--   The Bad Share construction uses the sum prime Power Parts le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumLeProdOfTwoLeNat.lean#L37-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumLeProdOfTwoLeNat.lean#L37-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumLeProdOfTwoLeNat
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

theorem GlobalTheory.BadShare.sum_primePowerParts_le :
    ∀ n q d : ℕ, 0 < n → q.Prime → d.Prime → q ≠ 2 → d ≠ 2 → q ≠ d → 16 ≤ max q d →
      16 * q * d ∣ n → (∑ l ∈ n.primeFactors, ((l ^ padicValNat l n : ℕ) : ℝ)) ≤
        (n : ℝ) / (4 * ((min q d : ℕ) : ℝ)) := by sorry
