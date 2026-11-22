-- Prove2me | Theorems.Thm_LLexpr_eval_inf
-- name    : LLexpr.eval_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:18.625926+00:00
-- url     : https://prove2.me/theorems/923d6859-0e0e-4c9b-80b1-b3c85e50b3ca
-- title:
--   LLexpr: eval inf
-- statement:
--   The LLexpr construction uses the eval inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L90-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L90-L91

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

theorem LLexpr.eval_inf (x : Fin n → X) (e₁ e₂ : LLexpr n) :
    eval x (.inf e₁ e₂) = eval x e₁ ⊓ eval x e₂ := by sorry

attribute [defeq] LLexpr.eval_inf
