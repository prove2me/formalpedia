-- Prove2me | Theorems.Thm_OAI_SevenEighths_CubicSieve_operator_conjugate_apply
-- name    : OAI.SevenEighths.CubicSieve.operator_conjugate_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:53.231695+00:00
-- url     : https://prove2.me/theorems/4a139ae6-7a22-402f-9acd-d4f492e37a42
-- title:
--   Cubic Sieve: operator conjugate apply
-- statement:
--   The Cubic Sieve construction uses the operator conjugate apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/Operator.lean#L35-L42
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/Operator.lean#L35-L42

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [DecidableEq m]

theorem OAI.SevenEighths.CubicSieve.operator_conjugate_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    operator (fun i j => star (A i j)) x = conjugateVector (operator A (conjugateVector x)) := by sorry
