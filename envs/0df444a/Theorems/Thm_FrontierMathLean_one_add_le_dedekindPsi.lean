-- Prove2me | Theorems.Thm_FrontierMathLean_one_add_le_dedekindPsi
-- name    : FrontierMathLean.one_add_le_dedekindPsi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:46:25.162592+00:00
-- url     : https://prove2.me/theorems/44c3f1e6-442d-5714-8104-db74aede177b
-- title:
--   Frontier Math Lean: one add le dedekind Psi
-- statement:
--   The elementary lower bound `n + 1 ≤ ψ(n)` for `n ≥ 2`.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1.lean#L59-L80
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1.lean#L59-L80

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

theorem FrontierMathLean.one_add_le_dedekindPsi {n : ℕ} (hn : 2 ≤ n) : n + 1 ≤ dedekindPsi n := by sorry
