-- Prove2me | Theorems.Thm_LLexpr_eval_smul
-- name    : LLexpr.eval_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:10.770116+00:00
-- url     : https://prove2.me/theorems/64404e42-18b8-494f-934f-893913ce7251
-- title:
--   LLexpr: eval smul
-- statement:
--   The LLexpr construction uses the eval smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L84-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L84-L85

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
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

theorem LLexpr.eval_smul (x : Fin n → X) (r : ℝ) (e : LLexpr n) :
    eval x (.smul r e) = r • eval x e := by sorry

attribute [defeq] LLexpr.eval_smul
