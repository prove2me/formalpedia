-- Prove2me | Theorems.Thm_OddPerfectNumber_sigma_external_prime_mem_or_eq_p_v2
-- name    : OddPerfectNumber.sigma_external_prime_mem_or_eq_p_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T01:22:35.785526+00:00
-- url     : https://prove2.me/theorems/e2073bd7-5a29-40af-99d3-25484f53f4a4
-- title:
--   External prime divisor of sigma lies in m or equals p (corrected)
-- statement:
--   Same as v1 but with p.Prime, which is required for the r=p alternative.
-- source:
--   Correction of v1 which omitted hp:p.Prime and was therefore unprovable as stated. v1 retained as malformed record.

import Mathlib

namespace OddPerfectNumber

theorem sigma_external_prime_mem_or_eq_p_v2 (p m d sigma r : Nat)
    (hp : p.Prime)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hr : r.Prime)
    (hdiv : r ∣ sigma) :
    r ∣ m ∨ r = p := by sorry

end OddPerfectNumber
