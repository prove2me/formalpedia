-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_absurd_canonical_coordinates_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_absurd_canonical_coordinates_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-18T11:34:03.556537+00:00
-- url     : https://prove2.me/theorems/2d9cb9ea-cf98-45c1-918b-abeff554c6e2
-- title:
--   The q3=17 branch is impossible with structural factorization coordinates
-- statement:
--   Let p be prime with p congruent to 1 modulo 4, let m be odd with p not dividing m, and let m^2=((p+1)/2)d and its divisor sum equal pd. Let q4>17 be prime, and let every prime factor of m belong to {3,5,17,q4}. Suppose m^2=3^(2a)5^(2b)17^(2c)q4^(2e) with positive half exponents a,b,c,e. Let sigma equal both the divisor sum of m^2 and the corresponding product of four geometric sums. Suppose the prime-factor memberships and factorization coordinates at 3,5,17 agree with that representation. Then these data are impossible: False. This all-range branch theorem requires no numerical exponent floors, D range, source hypotheses, or finite tuple.
-- source:
--   Canonical q17 branch target mirroring the proved q19 coordinates interface; consumes D-case reductions + proved order certificates.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_absurd_canonical_coordinates_v1 (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 17 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 17 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 17 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 17 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h17mem : 17 ∈ (m ^ 2).primeFactors)
    (h17exp : (m ^ 2).factorization 17 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    False := by sorry

end OddPerfectNumber
