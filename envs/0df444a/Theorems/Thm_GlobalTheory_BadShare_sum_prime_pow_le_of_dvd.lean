-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_sum_prime_pow_le_of_dvd
-- name    : GlobalTheory.BadShare.sum_prime_pow_le_of_dvd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:49.14736+00:00
-- url     : https://prove2.me/theorems/9418aebf-a8cd-40e1-8107-0ab5ff8cbf4e
-- title:
--   Bad Share: sum prime pow le of dvd
-- statement:
--   The Bad Share construction uses the sum prime pow le of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumPrimePowerPartPowSubOneLe.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumPrimePowerPartPowSubOneLe.lean#L39-L44

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

theorem GlobalTheory.BadShare.sum_prime_pow_le_of_dvd (s : Finset ℕ) (e : ℕ → ℕ) (M : ℕ) (hM : M ≠ 0)
    (hp : ∀ l ∈ s, l.Prime) (he : ∀ l ∈ s, e l ≠ 0) (hd : ∀ l ∈ s, l ^ e l ∣ M) :
    ∑ l ∈ s, l ^ e l ≤ M := by sorry
