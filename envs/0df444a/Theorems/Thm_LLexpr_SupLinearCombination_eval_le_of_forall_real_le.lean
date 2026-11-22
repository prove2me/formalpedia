-- Prove2me | Theorems.Thm_LLexpr_SupLinearCombination_eval_le_of_forall_real_le
-- name    : LLexpr.SupLinearCombination.eval_le_of_forall_real_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:18.830721+00:00
-- url     : https://prove2.me/theorems/6cd77ae9-e6b3-4491-bf2e-7b7b071c498f
-- title:
--   Sup Linear Combination: eval le of forall real le
-- statement:
--   If one finite supremum of linear combinations is pointwise below another on
--   `ℝ^n`, then the same inequality holds after evaluation in any vector lattice.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L334-L343
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L334-L343

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

theorem LLexpr.SupLinearCombination.eval_le_of_forall_real_le {X : Type*} [AddCommGroup X]
    [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X] (A B : SupLinearCombination n)
    (h : ∀ r : Fin n → ℝ, A.eval r ≤ B.eval r) (x : Fin n → X) :
    A.eval x ≤ B.eval x := by sorry
