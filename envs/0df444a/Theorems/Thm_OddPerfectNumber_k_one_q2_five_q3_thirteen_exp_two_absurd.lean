-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp_two_absurd
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirteen_exp_two_absurd
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T18:56:27.667694+00:00
-- url     : https://prove2.me/theorems/4cbbb39e-2df9-4979-9873-2b6a8f6f7428
-- title:
--   The q2=5 q3=13 exponent-two large-q4 subcase is impossible
-- statement:
--   In the canonical k=1 equations, suppose every prime divisor of m is one of 3, 5, 13, q4 with q4>31, and the exponent of 5 in m^2 is exactly 2. Then this four-support subcase is impossible.
-- source:
--   The accepted local sigma-factor lemma gives divisibility of the exponent-two local sum into the global sum. The exact identity sigma(5^2)=31 and the accepted external-31 support certificate yield the contradiction.

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_external_thirty_one_absurd

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirteen_exp_two_absurd (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2) :
    False := by sorry

end OddPerfectNumber
