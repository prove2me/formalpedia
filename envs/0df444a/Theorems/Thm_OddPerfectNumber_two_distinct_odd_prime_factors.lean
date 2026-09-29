-- Prove2me | Theorems.Thm_OddPerfectNumber_two_distinct_odd_prime_factors
-- name    : OddPerfectNumber.two_distinct_odd_prime_factors
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T09:28:49.453983+00:00
-- url     : https://prove2.me/theorems/c724e900-a1a2-41b7-963d-961cd50f908c
-- title:
--   Two distinct odd prime divisors from a cardinality bound
-- statement:
--   If $k+1$ has at least two odd prime factors (counted with $2$ erased), then there are two distinct odd primes $q_1 \neq q_2$ both dividing $k+1$. This turns the cardinality hypothesis of the thirteen-residual into the usable witnesses its per-prime analysis needs.
-- source:
--   Dris cofactor analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem two_distinct_odd_prime_factors (k : Nat)
    (hk1 : 2 ≤ ((k + 1).primeFactors.erase 2).card) :
    ∃ q1 q2, q1 ≠ q2 ∧ q1.Prime ∧ q2.Prime ∧ Odd q1 ∧ Odd q2 ∧
      q1 ∣ k + 1 ∧ q2 ∣ k + 1 := by
  sorry

end OddPerfectNumber
