-- Prove2me | Theorems.Thm_LLexpr_NormalForm_eval_inf
-- name    : LLexpr.NormalForm.eval_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:36.037123+00:00
-- url     : https://prove2.me/theorems/ce97f852-9b04-498a-a576-b933d03a34a2
-- title:
--   Normal Form: eval inf
-- statement:
--   Evaluation turns infimum of normal forms into lattice infimum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L462-L465
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L462-L465

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

theorem LLexpr.NormalForm.eval_inf {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (N M : NormalForm n) (x : Fin n → X) :
    (inf N M).eval x = N.eval x ⊓ M.eval x := by sorry
