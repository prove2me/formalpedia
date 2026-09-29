-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_absurd_canonical_coordinates_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_canonical_coordinates_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T17:04:36.923661+00:00
-- url     : https://prove2.me/theorems/9d0d0330-2d7e-47b4-bee7-318d713cc3a7
-- title:
--   The q3=23 branch is impossible with structural factorization coordinates
-- statement:
--   Let p be prime, congruent to 1 modulo 4, and let m be odd with p not dividing m. Suppose m²=((p+1)/2)d and the divisor sum of m² equals pd. Let q4>23 be prime, with every prime divisor of m in {3,5,23,q4}. Write m²=3^(2a)5^(2b)23^(2c)q4^(2e), where a,b,c,e are positive half exponents, and let sigma equal both the divisor sum and the corresponding product of four geometric sums. Assume the prime-factor memberships and factorization coordinates at 3,5,23 agree with this representation. Then these data are impossible.
--
--   $$\mathrm{False}.$$
--
--   This is the all-range q3=23 contradiction with structural coordinates only. It exposes no derived numerical exponent floors, D range, fourth-prime divisibility condition, finite tuple, or source assumption. Application from a support-cardinality statement still requires extraction of the structural coordinates.
-- source:
--   Canonical interface repair of OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_half_floors_v2, UUID b6b796df-419d-4d88-803f-a90d92ba1b30, exact live statement inspected 2026-09-17. Structural interface matches the independently Proved q3=19 canonical-coordinate branch (65188c08-3a6b-414d-b909-65fc6bf089fd) with third prime 23. Local sigma-support restrictions exclude small full exponents 2,4,6 for 3 and 2,4 for 5; the separate 23 floor is Proved as 8cd2c825-abdf-4b80-97ed-8000dd84b568. No dependency points back to this newly proposed parent.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_terms_exact_v4
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate
import Theorems.Thm_OddPerfectNumber_order_three_mod_five_eq_four
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_half_exp23_ge2_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_absurd_half_floors_v2

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentythree_absurd_canonical_coordinates_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h23mem : 23 ∈ (m ^ 2).primeFactors)
    (h23exp : (m ^ 2).factorization 23 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) : False := by sorry

end OddPerfectNumber
