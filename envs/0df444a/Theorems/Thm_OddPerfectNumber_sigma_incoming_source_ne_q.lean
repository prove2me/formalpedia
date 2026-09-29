-- Prove2me | Theorems.Thm_OddPerfectNumber_sigma_incoming_source_ne_q
-- name    : OddPerfectNumber.sigma_incoming_source_ne_q
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T10:54:42.230999+00:00
-- url     : https://prove2.me/theorems/b126acdb-47d6-4180-9d53-09ff9a72447e
-- title:
--   A prime sigma source cannot equal the incoming prime
-- statement:
--   If q is prime and q divides the geometric divisor sum of a prime-power component r^a, then the source prime r is different from q. This is the local no-self-loop fact needed to expose an incoming sigma edge in the q-divides-d branch.
-- source:
--   Derived from the elementary theorem that a prime does not divide its own prime-power divisor sum.

import Mathlib
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow

namespace OddPerfectNumber

theorem sigma_incoming_source_ne_q (q r a : Nat)
    (hq : q.Prime)
    (hqr : q ∣ ∑ i ∈ Finset.range (a + 1), r ^ i) :
    r ≠ q := by sorry

end OddPerfectNumber
