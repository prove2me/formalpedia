-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_dvd_sigma
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_dvd_sigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T01:29:20.278064+00:00
-- url     : https://prove2.me/theorems/a8a73a2f-8427-4db9-a796-739b5f2c7e01
-- title:
--   A small D and a sixth power of five force five into the sigma value
-- statement:
--   In the canonical product and sigma equations, if D=(p+1)/2 is below 185 and 5^6 divides m^2, then 5 divides sigma.
-- source:
--   Exact prime-power divisibility and cross-multiplication; no odd-perfect-specific theorem is assumed.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_127_five_dvd_sigma (p m d sigma : Nat)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsigma : sigma = p * d)
    (hD : (p + 1) / 2 < 185)
    (hpow : 5 ^ 6 ∣ m ^ 2) :
    5 ∣ sigma := by
  sorry

end OddPerfectNumber
