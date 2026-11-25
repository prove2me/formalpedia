-- Prove2me | Theorems.Thm_FrontierMathLean_one_add_le_sigmaOne
-- name    : FrontierMathLean.one_add_le_sigmaOne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T08:46:37.711716+00:00
-- url     : https://prove2.me/theorems/a5f99c18-317d-4daf-b663-9b8e61e9e1da
-- title:
--   Frontier Math Lean: one add le sigma One
-- statement:
--   The elementary lower bound `n + 1 ≤ σ(n)` for the sum-of-divisors function.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1.lean#L83-L102
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1.lean#L83-L102

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

theorem FrontierMathLean.one_add_le_sigmaOne {n : ℕ} (hn : 2 ≤ n) :
    n + 1 ≤ ArithmeticFunction.sigma 1 n := by sorry
