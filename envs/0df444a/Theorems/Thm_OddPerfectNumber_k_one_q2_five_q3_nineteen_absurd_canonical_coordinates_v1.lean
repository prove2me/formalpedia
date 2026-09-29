-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_absurd_canonical_coordinates_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_absurd_canonical_coordinates_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T11:00:40.797902+00:00
-- url     : https://prove2.me/theorems/65188c08-3a6b-414d-b909-65fc6bf089fd
-- title:
--   The q3=19 branch is impossible with structural factorization coordinates
-- statement:
--   Let p be prime with p congruent to 1 modulo 4, let m be odd with p not dividing m, and let m²=((p+1)/2)d and its divisor sum equal pd. Let q4>19 be prime, and let every prime factor of m belong to {3,5,19,q4}. Suppose m²=3^(2a)5^(2b)19^(2c)q4^(2e) with positive half exponents a,b,c,e. Let sigma equal both the divisor sum of m² and the corresponding product of four geometric sums. Suppose the prime-factor memberships and factorization coordinates at 3,5,19 agree with that representation. Then these data are impossible:
--
--   $$\mathrm{False}.$$
--
--   This all-range branch theorem requires no numerical exponent floors, D range, source hypotheses, or finite tuple. Its explicit structural factorization coordinates must still be supplied when applying it from a support-cardinality statement.
-- source:
--   Composition of live accepted Prove2Me records: half-floor theorems 72c55739-a447-4782-a9a8-808554edf380, d949a7d7-1432-4f27-bd52-0e20d5754a77, 3aa823a4-c88e-4291-8af7-ff2d28d7f91a and all-range terminal 032cf8a5-9aaf-4cad-99a9-121a9566c876. Exact binders inspected 2026-09-17. Set D=(p+1)/2 and derive its support from m²=Dd. No new finite arithmetic or order certificates.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp3_ge4_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp3_ge3_exp5_ge3_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_half_exp19_ge2_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_absurd_v6

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_absurd_canonical_coordinates_v1 (p m d q4 a b c e sigma : Nat)
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
    False := by sorry

end OddPerfectNumber
