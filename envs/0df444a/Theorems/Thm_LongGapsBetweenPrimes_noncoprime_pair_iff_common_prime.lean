-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_noncoprime_pair_iff_common_prime
-- name    : LongGapsBetweenPrimes.noncoprime_pair_iff_common_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:39.977827+00:00
-- url     : https://prove2.me/theorems/54d07168-0856-46bb-b20b-def23ea2f55a
-- title:
--   Long Gaps Between Primes: noncoprime pair iff common prime
-- statement:
--   Failure of pairwise coprimality is witnessed by a shared prime factor.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1910-L1920
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1910-L1920

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.noncoprime_pair_iff_common_prime {P k : ℕ} (hP : P ≠ 0) (r : DivisorTuple P k) :
    (¬∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) ↔
      ∃ p : P.primeFactors, ∃ i j, i ≠ j ∧ p.val ∣ (r i).val ∧ p.val ∣ (r j).val := by sorry
