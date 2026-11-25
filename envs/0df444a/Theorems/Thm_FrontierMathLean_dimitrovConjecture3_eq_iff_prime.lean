-- Prove2me | Theorems.Thm_FrontierMathLean_dimitrovConjecture3_eq_iff_prime
-- name    : FrontierMathLean.dimitrovConjecture3_eq_iff_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:55:16.519246+00:00
-- url     : https://prove2.me/theorems/2401a157-be88-4598-966a-116fe79a88b4
-- title:
--   Frontier Math Lean: dimitrov Conjecture3 eq iff prime
-- statement:
--   Equality in the exact rational statement of Dimitrov's Conjecture 3 holds
--   if and only if `n` is prime.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture3Equality.lean#L178-L204
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture3Equality.lean#L178-L204

import Definitions.Def_FrontierMathLean_DimitrovConjecture3
import Definitions.Def_FrontierMathLean_DimitrovConjecture3Equality
set_option autoImplicit false
open scoped ArithmeticFunction.sigma
open FrontierMathLean

theorem FrontierMathLean.dimitrovConjecture3_eq_iff_prime
    (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    ((4 * ((n : ℚ) + 1) ^ (2 * k)
            + (((n : ℚ) ^ 2 - 1) ^ k)
            + ((n : ℚ) - 1) ^ (2 * k)) /
          (2 * (((n : ℚ) + 1) ^ (2 * k)
            + (((n : ℚ) ^ 2 - 1) ^ k))) =
        (n.totient : ℚ) ^ k /
            ((dedekindPsi n : ℚ) ^ k
              + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) +
          (dedekindPsi n : ℚ) ^ k /
            ((n.totient : ℚ) ^ k
              + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) +
          (ArithmeticFunction.sigma 1 n : ℚ) ^ k /
            ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k)) ↔
      n.Prime := by sorry
