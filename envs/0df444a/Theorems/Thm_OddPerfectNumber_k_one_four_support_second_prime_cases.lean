-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_four_support_second_prime_cases
-- name    : OddPerfectNumber.k_one_four_support_second_prime_cases
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T19:00:32.477486+00:00
-- url     : https://prove2.me/theorems/1ee92258-b2a3-42d0-bc7d-93e12c62b055
-- title:
--   Finite second-prime split after the q2 bound
-- statement:
--   If the smallest ordered support prime is 3 and the second support prime is prime and at most 23, then it is one of 5, 7, 11, 13, 17, 19, or 23.
-- source:
--   Finite dispatcher for the accepted q2≤23 abundance bound. Substitute q1=3, use q1<q2 to get 4≤q2, enumerate the finite interval, and eliminate non-primes with norm_num.

import Mathlib

namespace OddPerfectNumber

theorem k_one_four_support_second_prime_cases (q1 q2 : Nat)
    (hq1 : q1.Prime) (hq2 : q2.Prime)
    (horder : q1 < q2) (hq1eq : q1 = 3) (hq2le : q2 ≤ 23) :
    q2 = 5 ∨ q2 = 7 ∨ q2 = 11 ∨ q2 = 13 ∨
      q2 = 17 ∨ q2 = 19 ∨ q2 = 23 := by sorry

end OddPerfectNumber
