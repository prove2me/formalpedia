-- Prove2me | Theorems.Thm_FrontierMathLean_dimitrovConjecture1
-- name    : FrontierMathLean.dimitrovConjecture1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:50:41.831989+00:00
-- url     : https://prove2.me/theorems/cda48e57-c61c-4a2e-8b93-236560d1c88b
-- title:
--   Frontier Math Lean: dimitrov Conjecture1
-- statement:
--   **Dimitrov's Conjecture 1** from arXiv:2606.12484, formalized over `ℚ` (and hence equivalently
--   over `ℝ`).
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1.lean#L143-L154
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1.lean#L143-L154

import Definitions.Def_FrontierMathLean_ThreeTermInequality
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Definitions.Def_FrontierMathLean_DimitrovConjecture1
set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open FrontierMathLean

theorem FrontierMathLean.dimitrovConjecture1 (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (5 * ((n : ℚ) ^ 2 - 1) ^ k
          + 2 * ((n : ℚ) + 1) ^ (2 * k)
          + 2 * ((n : ℚ) - 1) ^ (2 * k)) /
        (((n : ℚ) ^ 2 - 1) ^ k) ≤
      ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k
          + (ArithmeticFunction.sigma 1 n : ℚ) ^ k) *
        (((n.totient : ℚ) ^ k)⁻¹ + ((dedekindPsi n : ℚ) ^ k)⁻¹
          + ((ArithmeticFunction.sigma 1 n : ℚ) ^ k)⁻¹) := by sorry
