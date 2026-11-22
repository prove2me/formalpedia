-- Prove2me | Theorems.Thm_LLexpr_SupLinearCombination_eval_add
-- name    : LLexpr.SupLinearCombination.eval_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:17.215408+00:00
-- url     : https://prove2.me/theorems/cdec5670-8714-4c2f-bc3b-35ed68524fcb
-- title:
--   Sup Linear Combination: eval add
-- statement:
--   Evaluation turns addition of finite suprema into addition in the vector lattice.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L205-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L205-L214

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

theorem LLexpr.SupLinearCombination.eval_add {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (A B : SupLinearCombination n)
    (x : Fin n → X) :
    (A.add B).eval x = A.eval x + B.eval x := by sorry
