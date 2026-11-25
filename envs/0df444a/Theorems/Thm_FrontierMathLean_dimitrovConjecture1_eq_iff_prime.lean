-- Prove2me | Theorems.Thm_FrontierMathLean_dimitrovConjecture1_eq_iff_prime
-- name    : FrontierMathLean.dimitrovConjecture1_eq_iff_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:51:12.180583+00:00
-- url     : https://prove2.me/theorems/f8569ff3-f74b-434d-8b62-5a8415fbc4ef
-- title:
--   Frontier Math Lean: dimitrov Conjecture1 eq iff prime
-- statement:
--   Equality in the exact rational statement of Dimitrov's Conjecture 1 holds
--   if and only if `n` is prime.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1Equality.lean#L229-L249
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1Equality.lean#L229-L249

import Definitions.Def_FrontierMathLean_DimitrovConjecture1
import Definitions.Def_FrontierMathLean_DimitrovConjecture1Equality
set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open FrontierMathLean

theorem FrontierMathLean.dimitrovConjecture1_eq_iff_prime (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (5 * ((n : ℚ) ^ 2 - 1) ^ k
          + 2 * ((n : ℚ) + 1) ^ (2 * k)
          + 2 * ((n : ℚ) - 1) ^ (2 * k)) /
        (((n : ℚ) ^ 2 - 1) ^ k) =
      ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k
          + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) *
        (((n.totient : ℚ) ^ k)⁻¹ + ((dedekindPsi n : ℚ) ^ k)⁻¹
          + ((ArithmeticFunction.sigma 1 n : ℚ) ^ k)⁻¹) ↔
      n.Prime := by sorry
