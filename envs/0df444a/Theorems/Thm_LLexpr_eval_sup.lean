-- Prove2me | Theorems.Thm_LLexpr_eval_sup
-- name    : LLexpr.eval_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:55.513561+00:00
-- url     : https://prove2.me/theorems/5507b316-9cf8-4ed2-94ed-023a2204d2af
-- title:
--   LLexpr: eval sup
-- statement:
--   The LLexpr construction uses the eval sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L87-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L87-L88

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

theorem LLexpr.eval_sup (x : Fin n → X) (e₁ e₂ : LLexpr n) :
    eval x (.sup e₁ e₂) = eval x e₁ ⊔ eval x e₂ := by sorry

attribute [defeq] LLexpr.eval_sup
