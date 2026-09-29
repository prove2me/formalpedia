-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp_four_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_exp_four_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T18:53:14.448778+00:00
-- url     : https://prove2.me/theorems/613b009b-435d-44fe-9208-d98502c0ef4e
-- title:
--   The q2=5 q3=13 exponent-four subcase is impossible
-- statement:
--   In the canonical k=1 equations, suppose every prime divisor of m is one of 3, 5, 13, q4 with q4>13, and the exponent of 5 in m^2 is exactly 4. Then this four-support subcase is impossible.
-- source:
--   Use the accepted local sigma-factor divisibility theorem at n=m^2 and q=5. The factorization hypothesis rewrites its exponent to 4, yielding the hlocal premise of the accepted four-support 5^4 contradiction certificate.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_five_exp_four_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_exp_four_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 13 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 4) :
    False := by sorry

end OddPerfectNumber
