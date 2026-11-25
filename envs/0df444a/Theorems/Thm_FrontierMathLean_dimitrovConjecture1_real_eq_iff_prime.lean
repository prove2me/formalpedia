-- Prove2me | Theorems.Thm_FrontierMathLean_dimitrovConjecture1_real_eq_iff_prime
-- name    : FrontierMathLean.dimitrovConjecture1_real_eq_iff_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:51:21.298595+00:00
-- url     : https://prove2.me/theorems/169be788-5ecd-48ea-aeab-7212d1ee772b
-- title:
--   Frontier Math Lean: dimitrov Conjecture1 real eq iff prime
-- statement:
--   Equality in the real-valued form of Dimitrov's bound holds exactly for primes.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1Equality.lean#L146-L225
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1Equality.lean#L146-L225

import Definitions.Def_FrontierMathLean_DimitrovConjecture1
import Definitions.Def_FrontierMathLean_DimitrovConjecture1Equality
set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open FrontierMathLean

theorem FrontierMathLean.dimitrovConjecture1_real_eq_iff_prime (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (5 * ((n : ℝ) ^ 2 - 1) ^ k
          + 2 * ((n : ℝ) + 1) ^ (2 * k)
          + 2 * ((n : ℝ) - 1) ^ (2 * k)) /
        (((n : ℝ) ^ 2 - 1) ^ k) =
      ((n.totient : ℝ) ^ k + (dedekindPsi n : ℝ) ^ k
          + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) *
        (((n.totient : ℝ) ^ k)⁻¹ + ((dedekindPsi n : ℝ) ^ k)⁻¹
          + ((ArithmeticFunction.sigma 1 n : ℝ) ^ k)⁻¹) ↔
      n.Prime := by sorry
