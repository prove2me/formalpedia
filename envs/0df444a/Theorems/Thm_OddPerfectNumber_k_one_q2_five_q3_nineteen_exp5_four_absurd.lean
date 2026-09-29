-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_four_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_four_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T23:07:49.317097+00:00
-- url     : https://prove2.me/theorems/a3e47e33-9ca2-4675-939d-29e1939d5527
-- title:
--   The exponent-four 5-component is impossible in the q2=5 q3=19 branch
-- statement:
--   Sigma(5^4) is divisible by 11. Support closure forces 11 to be p or one of 3,5,19,q4; the latter are impossible and p=11 contradicts p ≡ 1 mod 4.
-- source:
--   Use the local sigma-factor bridge, evaluate 11 | (1+5+25+125+625), apply four-support restriction, and eliminate all five role alternatives by exact arithmetic or the Euler congruence.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_exp5_four_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 4) :
    False := by sorry

end OddPerfectNumber
