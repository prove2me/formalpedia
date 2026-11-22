-- Prove2me | Theorems.Thm_LLexpr_eval_reindexExpr
-- name    : LLexpr.eval_reindexExpr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:19.410916+00:00
-- url     : https://prove2.me/theorems/fa7cb482-889e-4ca7-b796-e8b9fca1ab97
-- title:
--   LLexpr: eval reindex Expr
-- statement:
--   The LLexpr construction uses the eval reindex Expr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L94-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L94-L97

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

theorem LLexpr.eval_reindexExpr {m n : ℕ} (x : Fin m → X)
    (f : Fin n → Fin m) (e : LLexpr n) :
    eval x (reindexExpr f e) = eval (fun i => x (f i)) e := by sorry
