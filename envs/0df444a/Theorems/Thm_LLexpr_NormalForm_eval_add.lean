-- Prove2me | Theorems.Thm_LLexpr_NormalForm_eval_add
-- name    : LLexpr.NormalForm.eval_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:31.924511+00:00
-- url     : https://prove2.me/theorems/de61a645-3431-4006-9011-fd27d6747ad6
-- title:
--   Normal Form: eval add
-- statement:
--   Evaluation turns addition of normal forms into addition.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L431-L435
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L431-L435

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

theorem LLexpr.NormalForm.eval_add {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (N M : NormalForm n) (x : Fin n → X) :
    (add N M).eval x = N.eval x + M.eval x := by sorry
