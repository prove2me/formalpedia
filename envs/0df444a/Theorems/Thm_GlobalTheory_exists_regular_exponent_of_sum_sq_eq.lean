-- Prove2me | Theorems.Thm_GlobalTheory_exists_regular_exponent_of_sum_sq_eq
-- name    : GlobalTheory.exists_regular_exponent_of_sum_sq_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:41:18.185796+00:00
-- url     : https://prove2.me/theorems/40c67028-06c1-4e0c-836f-9090fef25dda
-- title:
--   Global Theory: exists regular exponent of sum sq eq
-- statement:
--   The Global Theory construction uses the exists regular exponent of sum sq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularExponentOfSumSqEq.lean#L5-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularExponentOfSumSqEq.lean#L5-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularExponentOfSumSqEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_regular_exponent_of_sum_sq_eq :
    ∀ (q d : ℕ) (a : ℕ → ℤ), 2 ≤ q → 0 < d →
      (∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l) →
      ∑ k ∈ Finset.range (q ^ d - 1), a k ^ 2 = d →
      (∀ s e l : ℕ, s * e = d → l * q ^ e ≡ l [MOD q ^ d - 1] → (s : ℤ) ∣ a l) →
      ∃ k : ℕ, a k ≠ 0 ∧ ∀ i : ℕ, 0 < i → i < d → ¬ k * q ^ i ≡ k [MOD q ^ d - 1] := by sorry
