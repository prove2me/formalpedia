-- Prove2me | Theorems.Thm_OddPerfectNumber_sq_factorization_even
-- name    : OddPerfectNumber.sq_factorization_even
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T09:22:59.942729+00:00
-- url     : https://prove2.me/theorems/37540038-e5e5-4bd9-8f38-20c0616dcf11
-- title:
--   Prime exponents in a square are even
-- statement:
--   The exponent of any prime $q$ in the factorization of a square $m^2$ is even. This parity structure lets later source-analysis arguments write the local exponent as $2e$ with $e$ the exponent in $m$.
-- source:
--   Valuation-flow analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem sq_factorization_even (m q : Nat) :
    Even ((m ^ 2).factorization q) := by
  sorry

end OddPerfectNumber
