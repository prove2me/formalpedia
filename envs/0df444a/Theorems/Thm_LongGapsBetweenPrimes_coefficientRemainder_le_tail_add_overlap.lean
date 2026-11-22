-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_coefficientRemainder_le_tail_add_overlap
-- name    : LongGapsBetweenPrimes.coefficientRemainder_le_tail_add_overlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:57.833595+00:00
-- url     : https://prove2.me/theorems/6cd4a2a9-2140-4296-88bd-cf596539da37
-- title:
--   Long Gaps Between Primes: coefficient Remainder le tail add overlap
-- statement:
--   Bound the coefficient remainder by the discarded tail and noncoprime mass.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2929-L2947
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L2929-L2947

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.coefficientRemainder_le_tail_add_overlap {P m : ℕ} (hP : 1 < P)
    (hm : 0 < m) {D : ℝ} (hcut : (m : ℝ) ≤ D) :
    coefficientRemainder P m D ≤
      (∑ d ∈ P.divisors.filter (fun d : ℕ => D / m < (d : ℝ)), |coefficient P d| / d.totient) +
      ∑ d ∈ P.divisors.filter (fun d => ¬d.Coprime m), |coefficient P d| / d.totient := by sorry
