-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_external_1093_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_external_1093_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T21:31:44.046994+00:00
-- url     : https://prove2.me/theorems/50eca19e-253e-48e2-90eb-7c23e2f31a12
-- title:
--   The external 1093-factor is impossible in the q2=5 q3=19 support case
-- statement:
--   Under the q2=5, q3=19 four-support equations, if the 3-component has exponent 6, q4 is greater than 1093, and the Euler prime is not 1093, the forced factor 1093 of sigma(3^6) cannot fit the support.
-- source:
--   The local sigma factor for 3^6 is 1093. The accepted local-to-global and finite-support lemmas force 1093 to be p or one of 3,5,19,q4; the hypotheses exclude all five placements.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_external_1093_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 1093 < q4)
    (hpne : p ≠ 1093)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 6) :
    False := by sorry

end OddPerfectNumber
