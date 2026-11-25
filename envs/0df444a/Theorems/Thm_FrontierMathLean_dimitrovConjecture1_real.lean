-- Prove2me | Theorems.Thm_FrontierMathLean_dimitrovConjecture1_real
-- name    : FrontierMathLean.dimitrovConjecture1_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:47:22.76958+00:00
-- url     : https://prove2.me/theorems/6a7029e7-6f43-4e0b-8745-4614edc6cdc2
-- title:
--   Frontier Math Lean: dimitrov Conjecture1 real
-- statement:
--   Dimitrov's Conjecture 1, first expressed over `ℝ` to apply the abstract inequality.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1.lean#L109-L137
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1.lean#L109-L137

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

theorem FrontierMathLean.dimitrovConjecture1_real (k n : ℕ) (_hk : 1 ≤ k) (hn : 2 ≤ n) :
    (5 * ((n : ℝ) ^ 2 - 1) ^ k
          + 2 * ((n : ℝ) + 1) ^ (2 * k)
          + 2 * ((n : ℝ) - 1) ^ (2 * k)) /
        (((n : ℝ) ^ 2 - 1) ^ k) ≤
      ((n.totient : ℝ) ^ k + (dedekindPsi n : ℝ) ^ k
          + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) *
        (((n.totient : ℝ) ^ k)⁻¹ + ((dedekindPsi n : ℝ) ^ k)⁻¹
          + ((ArithmeticFunction.sigma 1 n : ℝ) ^ k)⁻¹) := by sorry
