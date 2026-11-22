-- Prove2me | Theorems.Thm_LongGapsBetweenPrimes_coefficient_prime_incidence
-- name    : LongGapsBetweenPrimes.coefficient_prime_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:08.121119+00:00
-- url     : https://prove2.me/theorems/4ecd7bd6-5d60-4cd1-97aa-8aff359c54ee
-- title:
--   Long Gaps Between Primes: coefficient prime incidence
-- statement:
--   The incidence bound (3.7), with an explicit constant once |a(p)| ≤ 1.
--
--   Source: https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L862-L903
-- source:
--   https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L862-L903

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section

theorem LongGapsBetweenPrimes.coefficient_prime_incidence {P p : ℕ} (hP : 1 < P) (hsq : Squarefree P)
    (hp : p.Prime) (hpP : p ∣ P) (hcoeff : |coefficient P p| ≤ 1) :
    (∑ d ∈ P.divisors.filter (fun d => p ∣ d), |coefficient P d| / d.totient) ≤
      4 / (p : ℝ) := by sorry
