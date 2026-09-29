-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_dvd_sigma_v2
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_dvd_sigma_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T01:42:26.321995+00:00
-- url     : https://prove2.me/theorems/0b9feb85-3660-48ab-99ec-fbe7dd314d35
-- title:
--   A positive small D and a sixth power of five force five into sigma
-- statement:
--   In the product and sigma equations, if D=(p+1)/2 is positive and below 185 and 5^6 divides m^2, then 5 divides sigma.
-- source:
--   Exact prime-power divisibility with the necessary positivity hypothesis.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_127_five_dvd_sigma_v2 (p m d sigma : Nat)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsigma : sigma = p * d)
    (hDpos : 0 < (p + 1) / 2)
    (hD : (p + 1) / 2 < 185)
    (hpow : 5 ^ 6 ∣ m ^ 2) :
    5 ∣ sigma := by
  sorry

end OddPerfectNumber
