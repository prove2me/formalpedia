-- Prove2me | Theorems.Thm_OddPerfectNumber_k_succ_shape_of_card_le_one
-- name    : OddPerfectNumber.k_succ_shape_of_card_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T09:34:16.730847+00:00
-- url     : https://prove2.me/theorems/b354193b-72e8-404a-8385-d6ed610513b5
-- title:
--   Shape of k+1 with at most one odd prime factor
-- statement:
--   If $k+1$ has at most one odd prime factor, then $k+1 = 2^a q^b$ for some prime $q$ and exponents $a, b$. This multiplicative shape is the structural input the one-odd-prime core needs before running order/LTE arguments on $\sigma(p^k)$.
-- source:
--   Dris cofactor analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem k_succ_shape_of_card_le_one (k : Nat)
    (hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1) :
    ∃ a q b, q.Prime ∧ k + 1 = 2 ^ a * q ^ b := by
  sorry

end OddPerfectNumber
