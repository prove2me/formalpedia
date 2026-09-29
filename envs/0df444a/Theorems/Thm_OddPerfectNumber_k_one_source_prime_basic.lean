-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_source_prime_basic
-- name    : OddPerfectNumber.k_one_source_prime_basic
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T09:13:49.58751+00:00
-- url     : https://prove2.me/theorems/d6c76991-b1b3-46e2-850b-add0f3242eaa
-- title:
--   Basic facts about the distinguished source prime
-- statement:
--   Let $m$ be odd with $p \nmid m$ and let $q$ be a prime factor of $m^2$. Then $q$ is prime, $q$ divides $m$, $q \neq p$, and $q$ is odd. This packages the elementary prime-support facts about the distinguished source prime before the order-theoretic endgame.
-- source:
--   Valuation-flow endgame of the special-exponent k = 1 case of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem k_one_source_prime_basic (p m q : Nat)
    (hpm : ¬ p ∣ m) (hm_odd : Odd m)
    (hqmem : q ∈ (m ^ 2).primeFactors) :
    q.Prime ∧ q ∣ m ∧ q ≠ p ∧ Odd q := by
  sorry

end OddPerfectNumber
