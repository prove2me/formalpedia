-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp19_ge2_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exp19_ge2_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T10:24:59.481309+00:00
-- url     : https://prove2.me/theorems/3aa823a4-c88e-4291-8af7-ff2d28d7f91a
-- title:
--   The q3=19 half exponent of 19 is at least two
-- statement:
--   Let p be prime with p congruent to 1 modulo 4, and let m be odd with p not dividing m. Suppose m²=((p+1)/2)d and its divisor sum is pd. Suppose q4 is prime and greater than 19, and every prime factor of m belongs to {3,5,19,q4}. Write m²=3^(2a)5^(2b)19^(2c)q4^(2e), with positive half exponents a,b,c,e. Let sigma equal both the divisor sum of m² and the product of the four corresponding geometric sums. Assume the prime-factor memberships and factorization coordinates at 3,5,19 agree with these exponents. Then
--
--   $$c \ge 2.$$
--
--   Thus the full exponent of 19 is at least four. This supplies floor provenance for the four-support q3=19 branch without an external D range or source condition.
-- source:
--   Canonical-interface adapter for Prove2Me accepted 19-role theorem 8237a553-8e72-4ac6-8e3e-68533379a4ef, 3/5 half-floor adapter d949a7d7-1432-4f27-bd52-0e20d5754a77, geometric upper bound c7beccbd-6011-44fc-9a95-6d878b9470e0, and residual-five contradiction 2d651695-ab29-4b9b-a406-a2d5cd6d41c0. Toward nineteen_absurd_v6 (032cf8a5-9aaf-4cad-99a9-121a9566c876); no import of that parent. Exact statements inspected 2026-09-17.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_two_role
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_pow_dvd
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_absurd_from_sources_v4
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_three_v2
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_nineteen_v2
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_no_five_127_v2

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_half_exp19_ge2_v1 (p m d q4 a b c e sigma : Nat)
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
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    2 ≤ c := by sorry

end OddPerfectNumber
