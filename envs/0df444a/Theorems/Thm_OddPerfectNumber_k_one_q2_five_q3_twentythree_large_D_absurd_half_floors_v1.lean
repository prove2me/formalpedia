-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_absurd_half_floors_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_absurd_half_floors_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T12:59:15.971858+00:00
-- url     : https://prove2.me/theorems/9030b3ba-23ff-4890-a779-b3f9ca7b1130
-- title:
--   q3=23 large-D contradiction with full exponent floors 8,6,4,2
-- statement:
--   Let m,a,b,c,e,D,p,q4,sigma,d be natural numbers. Suppose the square part has ordered prime support 3,5,23,q4 and factorization m²=3^(2a)5^(2b)23^(2c)q4^(2e), with sigma its indicated geometric-sum product and its divisor sum. Suppose D sigma=p m², p=2D-1 is a prime congruent to 1 modulo 4, q4 is prime greater than 23, D has no prime divisor outside that support, sigma=p d, d divides m² and m is nonzero. Assume half-exponent bounds a≥4,b≥3,c≥2,e≥1. Then the large-D range is impossible:
--
--   $$D < 111.$$
--
--   This is a range-local terminal for the four-support branch. It has no fourth-prime-divides-D premise or assumed upper abundance window. The half-exponent bounds remain explicit and must be derived before using this result in a canonical branch theorem.
-- source:
--   Interface correction and composition of Prove2Me records f861b6fb-9e3c-44c5-8ef5-a7d9dcdd9930, dfcade0a-d794-4772-b044-3c5a663a0ad7, 834f2d19-9ddf-4292-8d8a-5ee4b1a55f16, ba67d32b-4b4c-4942-b989-c9c3c7a70b84 and 9923452f-daef-4a37-a86c-d1f060044aee. Upper-cut arithmetic reused from 5f928a16-0a57-4c9d-bbc8-dbad3fb7e7cf after removing unused stronger floors; full exponents are twice a,b,c,e.

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_gt_47_half_floors_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_q4_cases
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_nondivisor_half_floors_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_D_le_481_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_absurd_v3

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_large_D_absurd_half_floors_v1 (m a b c e D p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 111 ≤ D)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e)
    (hm0 : m ≠ 0) (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) : False := by sorry

end OddPerfectNumber
