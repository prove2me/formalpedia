-- Prove2me | Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
-- name    : LLexpr.SupLinearCombination.eval_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:22.948852+00:00
-- url     : https://prove2.me/theorems/e5169285-3fe9-453c-abdc-59e1431151d6
-- title:
--   Sup Linear Combination: eval smul
-- statement:
--   For non-negative scalars, evaluation turns coefficient scaling into scalar multiplication.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L240-L251
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L240-L251

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

theorem LLexpr.SupLinearCombination.eval_smul {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] {r : ℝ} (hr : 0 ≤ r)
    (A : SupLinearCombination n) (x : Fin n → X) :
    (A.smul r).eval x = r • A.eval x := by sorry
