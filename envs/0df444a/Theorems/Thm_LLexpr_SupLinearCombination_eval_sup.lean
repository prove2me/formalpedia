-- Prove2me | Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
-- name    : LLexpr.SupLinearCombination.eval_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:26.407918+00:00
-- url     : https://prove2.me/theorems/fe3d02b5-86c5-4334-95f1-a8438f40f364
-- title:
--   Sup Linear Combination: eval sup
-- statement:
--   Evaluation turns `SupLinearCombination.sup` into lattice supremum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L223-L229
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L223-L229

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

theorem LLexpr.SupLinearCombination.eval_sup {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (A B : SupLinearCombination n)
    (x : Fin n → X) :
    (A.sup B).eval x = A.eval x ⊔ B.eval x := by sorry
