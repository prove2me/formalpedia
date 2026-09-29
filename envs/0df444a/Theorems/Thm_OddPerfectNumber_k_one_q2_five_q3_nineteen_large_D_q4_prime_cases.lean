-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_q4_prime_cases
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_q4_prime_cases
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-15T08:10:14.504931+00:00
-- url     : https://prove2.me/theorems/812f8548-dfb8-4256-9e8a-8f964eae62da
-- title:
--   q3=19 large-D fourth-prime enumeration
-- statement:
--   A prime q4 with 19<q4≤113 is exactly one of the listed finite primes.
-- source:
--   Exact finite prime enumeration in the q3=19 large-D interval; no OPN-specific contradiction is introduced.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_large_D_q4_prime_cases (q4 : Nat) (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hq4le : q4 ≤ 113) : q4 = 23 ∨ q4 = 29 ∨ q4 = 31 ∨ q4 = 37 ∨ q4 = 41 ∨ q4 = 43 ∨ q4 = 47 ∨ q4 = 53 ∨ q4 = 59 ∨ q4 = 61 ∨ q4 = 67 ∨ q4 = 71 ∨ q4 = 73 ∨ q4 = 79 ∨ q4 = 83 ∨ q4 = 89 ∨ q4 = 97 ∨ q4 = 101 ∨ q4 = 103 ∨ q4 = 107 ∨ q4 = 109 ∨ q4 = 113 := by
  sorry

end OddPerfectNumber
