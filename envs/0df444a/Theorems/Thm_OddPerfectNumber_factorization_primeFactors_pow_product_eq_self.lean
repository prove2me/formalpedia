-- Prove2me | Theorems.Thm_OddPerfectNumber_factorization_primeFactors_pow_product_eq_self
-- name    : OddPerfectNumber.factorization_primeFactors_pow_product_eq_self
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-13T15:51:47.965139+00:00
-- url     : https://prove2.me/theorems/fff14d6f-7285-49e2-bb13-a4a3f897440d
-- title:
--   Prime-support factorization product reconstructs a nonzero natural
-- statement:
--   For every nonzero natural number, the product of each prime in its prime support raised to its factorization exponent reconstructs the number.
-- source:
--   Reusable factorization wrapper for the four-support proof, directly exposing Mathlib's prime-support reconstruction identity without any OPN-specific assumptions.

import Mathlib

namespace OddPerfectNumber

theorem factorization_primeFactors_pow_product_eq_self (n : Nat)
    (hn : n ≠ 0) :
    (∏ q ∈ n.primeFactors, q ^ n.factorization q) = n := by
  sorry

end OddPerfectNumber
