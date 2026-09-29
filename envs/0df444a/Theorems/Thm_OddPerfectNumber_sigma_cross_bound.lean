-- Prove2me | Theorems.Thm_OddPerfectNumber_sigma_cross_bound
-- name    : OddPerfectNumber.sigma_cross_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T12:22:44.015999+00:00
-- url     : https://prove2.me/theorems/4d059d7a-8dc4-4a69-a5d8-3459a4826d2d
-- title:
--   Global sigma cross bound
-- statement:
--   For every natural number n greater than one, the product of q minus one over the prime support times sigma(n) is strictly less than the product of q over the prime support times n.

import Mathlib

theorem OddPerfectNumber.sigma_cross_bound (n : Nat) (hn : 1 < n) :
    (∏ q ∈ n.primeFactors, (q - 1)) * ArithmeticFunction.sigma 1 n <
      (∏ q ∈ n.primeFactors, q) * n := by sorry
