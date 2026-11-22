-- Prove2me | Theorems.Thm_LLexpr_NormalForm_eval_negate
-- name    : LLexpr.NormalForm.eval_negate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:30.104795+00:00
-- url     : https://prove2.me/theorems/7870fdf3-31f0-4dea-a0a3-278f98698e7b
-- title:
--   Normal Form: eval negate
-- statement:
--   Evaluation turns negation of normal forms into negation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L438-L442
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L438-L442

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

theorem LLexpr.NormalForm.eval_negate {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (N : NormalForm n)
    (x : Fin n → X) :
    (negate N).eval x = -N.eval x := by sorry
