-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp3_ge4_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exp3_ge4_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T10:38:15.163974+00:00
-- url     : https://prove2.me/theorems/72c55739-a447-4782-a9a8-808554edf380
-- title:
--   The q3=19 half exponent of 3 is at least four
-- statement:
--   Let p be prime with p congruent to 1 modulo 4. Let m be odd with p not dividing m, and suppose m²=((p+1)/2)d and its divisor sum is pd. Suppose q4 is prime, q4>19, and every prime factor of m belongs to {3,5,19,q4}. Write m²=3^(2a)5^(2b)19^(2c)q4^(2e), with positive half exponents a,b,c,e. Let sigma equal both the divisor sum and the corresponding product of geometric sums. Assume prime-factor membership and factorization coordinates at 3 and 5 agree with that representation. Then
--
--   $$a \ge 4.$$
--
--   Equivalently, the full exponent at 3 is at least eight. This removes the specialised 547/1093 source premises from the exponent-six exclusion and supplies floor provenance for the q3=19 branch.
-- source:
--   Canonical adapter to nineteen_absurd_v6 (032cf8a5-9aaf-4cad-99a9-121a9566c876). Independently accepted dependencies: floor adapter d949a7d7-1432-4f27-bd52-0e20d5754a77, 1093 role f2be5f3d-cc54-4d83-ba6b-68784480acb2, geometric bound c7beccbd-6011-44fc-9a95-6d878b9470e0, residual-five 42add97d-4784-48fd-83eb-06b26cc4227a, product obstruction 8a9945fd-9881-427a-9990-5ae9077a2e5a. Exact statements read 2026-09-17; no import of the all-D parent or specialised two-arm wrapper.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_six_1093_role
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_three_v2
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_nineteen_v2
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_1093_no_five
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_1093_product_no_five

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_half_exp3_ge4_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    4 ≤ a := by sorry

end OddPerfectNumber
