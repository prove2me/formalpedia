-- Prove2me | Theorems.Thm_FrontierMathLean_totient_le_sub_one
-- name    : FrontierMathLean.totient_le_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:46:43.456047+00:00
-- url     : https://prove2.me/theorems/f37ce22a-551f-58b8-8591-2483dae256ae
-- title:
--   Frontier Math Lean: totient le sub one
-- statement:
--   The elementary upper bound `φ(n) ≤ n - 1` for `n ≥ 2`.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1.lean#L105-L106
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/DimitrovConjecture1.lean#L105-L106

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

theorem FrontierMathLean.totient_le_sub_one {n : ℕ} (hn : 2 ≤ n) : n.totient ≤ n - 1 := by sorry
