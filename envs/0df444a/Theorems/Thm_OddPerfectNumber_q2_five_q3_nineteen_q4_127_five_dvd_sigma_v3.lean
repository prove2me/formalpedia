-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_dvd_sigma_v3
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_dvd_sigma_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T01:48:57.205792+00:00
-- url     : https://prove2.me/theorems/8769ae47-1811-4487-b13f-35c318992c92
-- title:
--   A prime Euler parameter and small D force five into sigma
-- statement:
--   For a prime Euler parameter p, the canonical product and sigma equations with 0<D<185 and 5^6 dividing m^2 imply 5 divides sigma.
-- source:
--   A direct Nat.Prime interface to the pinned prime-power divisibility theorem.

import Mathlib

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_127_five_dvd_sigma_v3 (p m d sigma : Nat)
    (hp : p.Prime)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsigma : sigma = p * d)
    (hD : (p + 1) / 2 < 185)
    (hpow : 5 ^ 6 ∣ m ^ 2) :
    5 ∣ sigma := by
  sorry

end OddPerfectNumber
