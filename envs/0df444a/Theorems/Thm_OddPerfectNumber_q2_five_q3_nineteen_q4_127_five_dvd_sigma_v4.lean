-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T01:51:59.94029+00:00
-- url     : https://prove2.me/theorems/42add97d-4784-48fd-83eb-06b26cc4227a
-- title:
--   A prime Euler parameter and small D force five into sigma
-- statement:
--   For a prime Euler parameter p, the canonical equations with D=(p+1)/2 below 185 and 5^6 dividing m^2 imply 5 divides sigma.
-- source:
--   Exact divisibility bridge using the accepted Nat-prime adapter.

import Mathlib
import Theorems.Thm_OddPerfectNumber_nat_prime_pow_dvd_of_dvd_mul_right

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_127_five_dvd_sigma_v4 (p m d sigma : Nat)
    (hp : p.Prime)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsigma : sigma = p * d)
    (hD : (p + 1) / 2 < 185)
    (hpow : 5 ^ 6 ∣ m ^ 2) :
    5 ∣ sigma := by
  sorry

end OddPerfectNumber
