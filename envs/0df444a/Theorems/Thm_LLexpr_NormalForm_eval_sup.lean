-- Prove2me | Theorems.Thm_LLexpr_NormalForm_eval_sup
-- name    : LLexpr.NormalForm.eval_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:32.082489+00:00
-- url     : https://prove2.me/theorems/0be27a02-7dbb-4b5a-8095-f9c62affc233
-- title:
--   Normal Form: eval sup
-- statement:
--   Evaluation turns supremum of normal forms into lattice supremum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L456-L459
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L456-L459

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

theorem LLexpr.NormalForm.eval_sup {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (N M : NormalForm n) (x : Fin n → X) :
    (sup N M).eval x = N.eval x ⊔ M.eval x := by sorry
