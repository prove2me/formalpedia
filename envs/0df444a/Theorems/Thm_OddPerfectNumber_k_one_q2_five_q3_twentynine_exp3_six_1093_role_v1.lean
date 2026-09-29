-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_exp3_six_1093_role_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_twentynine_exp3_six_1093_role_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T23:53:48.696684+00:00
-- url     : https://prove2.me/theorems/c8594b97-8ff6-45ee-a144-819efc847417
-- title:
--   q3=29 full 3-exponent six forces 1093 as Euler or fourth prime
-- statement:
--   If the full 3-adic exponent of m^2 is six, then sigma(3^6)=1093 divides the divisor sum, so 1093 is the Euler prime or the fourth support prime.
-- source:
--   q3=29 analogue of the accepted q3=19 1093-role theorem. Minimal interface: no D, no floors. S(3,6)=1093 prime via norm_num; accepted local-sigma and sigma-prime-restriction close it.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_twentynine_exp3_six_1093_role_v1 (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 6) :
    p = 1093 ∨ q4 = 1093 := by sorry

end OddPerfectNumber
