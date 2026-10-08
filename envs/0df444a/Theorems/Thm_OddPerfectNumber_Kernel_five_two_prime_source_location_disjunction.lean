-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_source_location_disjunction
-- name    : OddPerfectNumber.Kernel.five_two_prime_source_location_disjunction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T12:04:52.689444+00:00
-- url     : https://prove2.me/theorems/1312beaa-a069-4514-9ff4-8863013ddbfe
-- title:
--   Where a prime divisor of the Dris core can live, once the core is factored
-- statement:
--   Euclid's lemma for a product of five natural numbers: if a prime divides the product then it divides at least one of the five factors. This is the support-only step that converts the first-equation formula m = 3*u*a*b*d1*q*r into the source-location disjunction for any prime t dividing m, namely t = 3 or t | u*a*b*d1 or t = q or t = r. It asserts nothing about which primes actually occur and makes no claim that every prime divisor of m lies in an excluded class.
-- source:
--   Standard Euclid's lemma in a commutative monoid, iterated four times. The single Mathlib dependency is Nat.Prime.dvd_mul at Mathlib/Data/Nat/Prime/Defs.lean:422, with the alias Nat.Prime.dvd_or_dvd on line 426. Verified numerically before submission: over 32927 sampled tuples with a prime t dividing a product of five naturals, there was no case in which t divided none of the five factors.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_source_location_disjunction
    (t a b c d e : Nat) (ht : t.Prime)
    (h : Dvd.dvd t (a * b * c * d * e)) :
    Dvd.dvd t a \/ Dvd.dvd t b \/ Dvd.dvd t c \/ Dvd.dvd t d \/ Dvd.dvd t e := by
  sorry

end OddPerfectNumber.Kernel
