-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_half_exp23_ge2_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_half_exp23_ge2_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T15:22:45.391733+00:00
-- url     : https://prove2.me/theorems/8cd2c825-abdf-4b80-97ed-8000dd84b568
-- title:
--   Canonical half exponent of 23 is at least two
-- statement:
--   Suppose p is prime and congruent to 1 modulo 4, m is odd, m²=((p+1)/2)d, and the divisor sum of m² is pd. Suppose every prime factor of m belongs to {3,5,23,q4}, with q4>23. If the factorization exponent of 23 in m² is 2c with c positive, then c is at least two. Here c is a half exponent; the conclusion is a full exponent of at least four. The excluded full exponent two would force the unavailable sigma prime 7 from 1+23+23²=553.
-- source:
--   Canonical q3=23 interface repair for OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_half_floors_v2 (b6b796df-419d-4d88-803f-a90d92ba1b30). Exact sigma-factor and support dependencies read live as Proved; source argument analogous to the accepted q3=19 small-exponent exclusions, with 7 dividing sigma(23²).

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_half_exp23_ge2_v1 (p m d q4 c : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hq4gt : 23 < q4)
    (h23mem : 23 ∈ (m ^ 2).primeFactors)
    (h23exp : (m ^ 2).factorization 23 = 2*c)
    (hc : 0 < c) : 2 ≤ c := by sorry

end OddPerfectNumber
