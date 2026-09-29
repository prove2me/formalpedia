-- Prove2me | Theorems.Thm_OddPerfectNumber_sigma_external_prime_mem_or_eq_p_v1
-- name    : OddPerfectNumber.sigma_external_prime_mem_or_eq_p_v1
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-18T01:20:34.204446+00:00
-- url     : https://prove2.me/theorems/fcafc7a3-dcbd-4eac-8e73-bcbc5b8804ea
-- title:
--   External prime divisor of sigma lies in m or equals p
-- statement:
--   If m^2=((p+1)/2)d, the divisor sum of m^2 equals p*d, sigma is that divisor sum, r is prime and r divides sigma, then r divides m or r equals p.
-- source:
--   Generic support-closure helper for finite four-support branches. Since sigma=p*d and d divides m^2, a prime divisor of sigma divides p (hence equals p if p prime... used via Nat prime dvd) or divides d hence m^2 hence m. No OPN-specific hypotheses.

import Mathlib

namespace OddPerfectNumber

theorem sigma_external_prime_mem_or_eq_p_v1 (p m d sigma r : Nat)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hr : r.Prime)
    (hdiv : r ∣ sigma) :
    r ∣ m ∨ r = p := by sorry

end OddPerfectNumber
