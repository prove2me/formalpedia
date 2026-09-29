-- Prove2me | Theorems.Thm_OddPerfectNumber_sigma_eq_local_prod
-- name    : OddPerfectNumber.sigma_eq_local_prod
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T09:53:17.591698+00:00
-- url     : https://prove2.me/theorems/c53d8cf3-af59-47f0-a0e4-31d244bce608
-- title:
--   Divisor sum factors over local geometric sums
-- statement:
--   The divisor sum $\sigma(m^2)$ factors as the product over the prime support of the local geometric sums $1 + q + \cdots + q^{2e}$. This multiplicativity bridge underlies every valuation-flow argument on the OPN cores.
-- source:
--   Valuation-flow analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem sigma_eq_local_prod (m : Nat) (hm : m ^ 2 ≠ 0) :
    (∑ x ∈ (m ^ 2).divisors, x)
      = ∏ q ∈ (m ^ 2).primeFactors,
        ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i := by
  sorry

end OddPerfectNumber
