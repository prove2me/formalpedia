-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exponent_floors_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_half_exponent_floors_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T16:25:52.371813+00:00
-- url     : https://prove2.me/theorems/17b9f1f2-ed2c-4664-88f5-15387295b096
-- title:
--   Canonical q3=19 half-exponent floors
-- statement:
--   Suppose p is prime with p ≡ 1 mod 4, m is odd, p does not divide m, m²=((p+1)/2)d, and the divisor sum of m² equals pd. Let q4>19 be prime and suppose every prime factor of m lies in {3,5,19,q4}. Write m²=3^(2a)·5^(2b)·19^(2c)·q4^(2e), with positive half exponents a,b,c,e and with sigma equal to both the divisor sum and the corresponding product of geometric sums. Then a≥4, b≥3, c≥2, and e≥1.
-- source:
--   Canonical q3=19 exponent-floor package. It imports the live Proved half-exponent bounds at 3 and 19, separately applies the accepted a>=3,b>=3 adapter, and obtains e>=1 from he by exact arithmetic. No new mathematical argument, order certificate, D range, tuple or source premise is introduced.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp3_ge4_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp19_ge2_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_half_exponent_floors_v1 (p m d q4 a b c e sigma : Nat)
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
    4 ≤ a ∧ 3 ≤ b ∧ 2 ≤ c ∧ 1 ≤ e := by sorry

end OddPerfectNumber
