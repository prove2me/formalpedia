-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_absurd_half_floors_v2
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_half_floors_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T14:31:17.547455+00:00
-- url     : https://prove2.me/theorems/b6b796df-419d-4d88-803f-a90d92ba1b30
-- title:
--   All-D q3=23 contradiction with full exponent floors 8,6,4,2
-- statement:
--   Let m²=3^(2a)5^(2b)23^(2c)q4^(2e), with sigma equal to both its geometric divisor-sum product and its divisor sum. Suppose D is odd, D sigma=p m², p=2D−1 is prime and congruent to 1 modulo 4, q4>23 is prime, and the prime divisors of D and m lie in {3,5,23,q4}. Suppose m is nonzero, sigma=p d, and d divides m². If the half exponents satisfy a≥4,b≥3,c≥2,e≥1, then these assumptions are contradictory.
--
--   There are no extra D-range or fourth-prime divisibility assumptions. The exponent floors remain hypotheses, so their derivation from canonical branch data is a separate obligation.
-- source:
--   Consolidated interface repair from accepted children f3d48e81-bac9-45b0-9415-9c5377bc178d, a86b8924-90e5-4ea4-a503-854c02573dff and 9030b3ba-23ff-4890-a779-b3f9ca7b1130. The private small divisor argument reuses accepted finite tuple and even-order certificates. Implements the user's requested correction to half floors 4,3,2,1 without claiming those floors follow from positivity.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_divides_D_cases_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_gt_47_half_floors_v1
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_even_orders_mod_157_q3_twentythree
import Theorems.Thm_OddPerfectNumber_even_orders_mod_193_q3_twentythree
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_small_D_lt_q4_absurd_half_floors_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_not_divides_D_absurd_half_floors_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_absurd_half_floors_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_absurd_half_floors_v2 (m a b c e D p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDodd : Odd D)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e)
    (hm0 : m ≠ 0) (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) : False := by sorry

end OddPerfectNumber
