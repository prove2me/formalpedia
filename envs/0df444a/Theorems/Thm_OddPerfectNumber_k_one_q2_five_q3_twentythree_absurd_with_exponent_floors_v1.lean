-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_absurd_with_exponent_floors_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_with_exponent_floors_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T09:42:21.810271+00:00
-- url     : https://prove2.me/theorems/ef13f319-4f46-4681-84e7-85336290d517
-- title:
--   q3=23 contradiction with exponent floors and no fourth-prime divisor premise
-- statement:
--   Let the square part have factorization m²=3^(2a)5^(2b)23^(2c)q4^(2e), where q4>23 is prime and a≥5,b≥3,c≥4,e≥1. Let sigma be both the product of the four local geometric sums and the divisor sum of m². Suppose D is odd, p=2D−1 is prime with p congruent to 1 modulo 4, and D sigma=p m². Suppose every prime divisor of D and m lies in {3,5,23,q4}, m is nonzero, and sigma=p d for a divisor d of m². Then these assumptions are inconsistent.
--
--   This combines both fourth-prime divisibility cases; it has no D-range, q4-divisibility, tuple or order assumption. The half-exponent floors remain explicit, so the theorem does not claim their derivation from merely positive exponents.
-- source:
--   Source-faithful strengthening of accepted OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_canonical_v13 (d97d0664-bdac-4cdf-bbe4-20e427aa39cb) by removing q4|D. Independent accepted nondivisor theorem a08ee1a6-1c0b-4331-a002-2855ab234903 and small-D terminal 0ecabd70-1289-4604-b5ba-813c43953553 supply the missing arms. Exact child binders and decomposition records inspected 2026-09-17; the new target is absent from all existing child graphs.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_absurd_canonical_v13
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_absurd_canonical_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_gt_47_adapter_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_q4_le_61_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_q4_cases
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_nondivisor_absurd_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_absurd_with_exponent_floors_v1 (m a b c e D p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDodd : Odd D)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e)
    (hm0 : m ≠ 0) (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) : False := by
  sorry

end OddPerfectNumber
