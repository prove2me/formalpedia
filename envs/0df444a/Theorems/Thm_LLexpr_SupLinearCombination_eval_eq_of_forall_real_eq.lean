-- Prove2me | Theorems.Thm_LLexpr_SupLinearCombination_eval_eq_of_forall_real_eq
-- name    : LLexpr.SupLinearCombination.eval_eq_of_forall_real_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:04.585898+00:00
-- url     : https://prove2.me/theorems/dc4aa8b4-0ae7-476b-bd70-64112fc88998
-- title:
--   Sup Linear Combination: eval eq of forall real eq
-- statement:
--   If two finite suprema of linear combinations agree pointwise on `ℝ^n`, then
--   they agree after evaluation in any vector lattice.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L347-L352
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L347-L352

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
open LLexpr.SupLinearCombination

theorem LLexpr.SupLinearCombination.eval_eq_of_forall_real_eq {X : Type*} [AddCommGroup X]
    [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X] (A B : SupLinearCombination n)
    (h : ∀ r : Fin n → ℝ, A.eval r = B.eval r) (x : Fin n → X) :
    A.eval x = B.eval x := by sorry
