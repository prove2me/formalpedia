-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_divisorProbability_prime_incidence
-- name    : LongGapsBetweenPrimes.divisorProbability_prime_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:41:33.313065+00:00
-- url     : https://prove2.me/theorems/2e2ffd87-4557-4ea6-bd09-37cb0d1ae799
-- title:
--   Long Gaps Between Primes: divisor Probability prime incidence
-- statement:
--   A prime divides a random divisor with probability at most `4 / p`.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1884-L1907
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1884-L1907

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.divisorProbability_prime_incidence {P p : ℕ} {β C : ℝ}
    (h : CoefficientEstimates P β C) (hp : p.Prime) (hpP : p ∣ P) :
    (∑ d : DivisorIndex P, divisorProbability P d * if p ∣ d.val then 1 else 0) ≤ 4 / (p : ℝ) := by sorry
