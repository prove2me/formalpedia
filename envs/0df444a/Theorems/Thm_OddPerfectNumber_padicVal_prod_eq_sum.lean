-- Prove2me | Theorems.Thm_OddPerfectNumber_padicVal_prod_eq_sum
-- name    : OddPerfectNumber.padicVal_prod_eq_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T10:00:33.047224+00:00
-- url     : https://prove2.me/theorems/643ccb05-1d51-4c40-bf00-7d989e598432
-- title:
--   Valuation of a product is the sum of valuations
-- statement:
--   The $r$-adic valuation of a finite product of nonzero naturals is the sum of the valuations. This turns the divisor-sum product bridge into the additive form an $r$-adic count needs.
-- source:
--   Valuation-flow analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem padicVal_prod_eq_sum (S : Finset ℕ) (f : ℕ → ℕ) (r : Nat)
    (hr : r.Prime) (hf : ∀ q ∈ S, f q ≠ 0) :
    padicValNat r (∏ q ∈ S, f q) = ∑ q ∈ S, padicValNat r (f q) := by
  sorry

end OddPerfectNumber
