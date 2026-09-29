-- Prove2me | Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow
-- name    : OddPerfectNumber.prime_not_dvd_own_sigma_prime_pow
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T10:50:26.604712+00:00
-- url     : https://prove2.me/theorems/658bb7bb-0117-4aa5-9139-108751447791
-- title:
--   A prime does not divide its own prime-power divisor sum
-- statement:
--   For a prime q and any natural exponent a, q does not divide the geometric divisor sum 1 + q + ... + q^a. This is the local non-loop fact needed to show an incoming sigma source in the q-divides-d branch cannot be q itself.
-- source:
--   Elementary geometric-sum congruence: the sum is congruent to 1 modulo q.

import Mathlib

namespace OddPerfectNumber

theorem prime_not_dvd_own_sigma_prime_pow (q a : Nat)
    (hq : q.Prime) :
    ¬ q ∣ ∑ i ∈ Finset.range (a + 1), q ^ i := by sorry

end OddPerfectNumber
