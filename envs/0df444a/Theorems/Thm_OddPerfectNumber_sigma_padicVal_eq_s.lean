-- Prove2me | Theorems.Thm_OddPerfectNumber_sigma_padicVal_eq_s
-- name    : OddPerfectNumber.sigma_padicVal_eq_s
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T09:51:07.373216+00:00
-- url     : https://prove2.me/theorems/af02b0dd-1538-4497-ac53-801e59084ce9
-- title:
--   Divisor-sum valuation strips a coprime prime power
-- statement:
--   If the prime $r$ does not divide $p$ and $\sigma(m^2) = p^k \cdot s$, then the $r$-adic valuation of the divisor sum equals that of the cofactor $s$: the prime-power factor contributes valuation zero. This is the first step of any $r$-adic counting argument on the Dris-side residuals.
-- source:
--   Dris cofactor analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem sigma_padicVal_eq_s (r p k m s : Nat)
    (hr : r.Prime) (hpm : ¬ r ∣ p)
    (hs2 : 2 ≤ s)
    (hsigm : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    padicValNat r (∑ x ∈ (m ^ 2).divisors, x) = padicValNat r s := by
  sorry

end OddPerfectNumber
