-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_b_one_e_two_absurd_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_e_two_absurd_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T01:51:40.668606+00:00
-- url     : https://prove2.me/theorems/81d42407-dac6-432b-a58e-18b679530040
-- title:
--   q3=29 b=1 e=2 kill
-- statement:
--   In canonical q3=29 coordinates with 5-half-exponent 1 and q4-half-exponent 2: impossible, via q4=31, 11 dividing sigma, and support closure (11 is 3 mod 4, outside support).
-- source:
--   q3=29 b=1 e-split leaf mirroring the e=1 kill: b=1->q4=31 (accepted), Phi5(31) 11-certificate (Open, enters as child at proof time), support-closure helper (Proved).

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_b_one_e_two_absurd_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h29mem : 29 ∈ (m ^ 2).primeFactors)
    (h29exp : (m ^ 2).factorization 29 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hb1 : b = 1) (he2 : e = 2) :
    False := by sorry

end OddPerfectNumber
