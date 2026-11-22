-- Prove2me | Theorems.Thm_LLexpr_normalize_eval
-- name    : LLexpr.normalize_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:39.187935+00:00
-- url     : https://prove2.me/theorems/5f0f9452-57fd-4d12-b88f-ad70f60490d1
-- title:
--   LLexpr: normalize eval
-- statement:
--   The normal form of an expression has the same evaluation as the expression.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L480-L483
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L480-L483

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

theorem LLexpr.normalize_eval {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (x : Fin n → X) (e : LLexpr n) :
    (normalize e).eval x = eval x e := by sorry
