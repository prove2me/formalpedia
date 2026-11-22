-- Prove2me | Theorems.Thm_LLexpr_NormalForm_eval_zero
-- name    : LLexpr.NormalForm.eval_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:25.359685+00:00
-- url     : https://prove2.me/theorems/0962c448-291e-49b8-8f15-372ed50d43a4
-- title:
--   Normal Form: eval zero
-- statement:
--   Evaluating the zero normal form gives zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L419-L422
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L419-L422

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
set_option autoImplicit true
@[expose] public section
public section
open LLexpr
open scoped BigOperators
variable {n : ℕ}
open LLexpr.NormalForm

theorem LLexpr.NormalForm.eval_zero {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (x : Fin n → X) :
    (zero : NormalForm n).eval x = 0 := by sorry
