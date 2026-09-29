-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_divisor_small_absurd_half_floors_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_divisor_small_absurd_half_floors_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T14:25:40.140961+00:00
-- url     : https://prove2.me/theorems/03da0c34-80ba-4b7a-885c-0e7845078bee
-- title:
--   Small-D fourth-prime divisor arm with corrected half floors
-- statement:
--   Let m²=3^(2a)5^(2b)23^(2c)q4^(2e), with sigma the corresponding product of divisor sums, D sigma=p m², and p=2D−1 prime. Suppose D is odd and less than 111, q4>23 is prime, and q4 divides D. If the half exponents satisfy a≥4,b≥3,c≥2,e≥1, these assumptions imply a contradiction. This is the divisor arm of the small-D branch, not a complete canonical branch.
-- source:
--   Interface weakening of the existing small divisor arm. Accepted finite cases 316a7281-c0bd-4e7b-8831-5b52741b8dfc and corrected lower cut f861b6fb-9e3c-44c5-8ef5-a7d9dcdd9930 leave (D,q4)=(79,79) or (97,97). Accepted order certificates 332319d7-23f4-4ef9-a780-6ce0b7120db5 and da67840f-06b8-47e5-9dee-0272bdaa1380 supply the unchanged terminal argument. No new finite enumeration or order computation.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_divides_D_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_gt_47_half_floors_v1
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_even_orders_mod_157_q3_twentythree
import Theorems.Thm_OddPerfectNumber_even_orders_mod_193_q3_twentythree

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_q4_divisor_small_absurd_half_floors_v1 (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 23 < q4) (hq4div : q4 ∣ D)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by sorry

end OddPerfectNumber
