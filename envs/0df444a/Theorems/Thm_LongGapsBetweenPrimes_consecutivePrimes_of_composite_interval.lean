-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_consecutivePrimes_of_composite_interval
-- name    : LongGapsBetweenPrimes.consecutivePrimes_of_composite_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:39.520742+00:00
-- url     : https://prove2.me/theorems/594e38c4-8782-4707-a069-20cce427eba4
-- title:
--   Long Gaps Between Primes: consecutive Primes of composite interval
-- statement:
--   The elementary passage from a prime-free interval to consecutive primes.
--   Bertrand's postulate supplies the upper endpoint bound used in Section 2.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L355-L371
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L355-L371

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.consecutivePrimes_of_composite_interval {N H : ℕ} (hN : 2 ≤ N)
    (hcomposite : ∀ n : ℕ, N < n → n ≤ N + H → ¬n.Prime) :
    ∃ p q : ℕ, ConsecutivePrimes p q ∧ p ≤ N ∧ N + H < q ∧ q ≤ 2 * N ∧ H < q - p := by sorry
