-- Prove2me | Theorems.Thm_LLexpr_eval_var
-- name    : LLexpr.eval_var
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:05.907027+00:00
-- url     : https://prove2.me/theorems/9166c21c-197d-4733-bace-f8dab0b14dbb
-- title:
--   LLexpr: eval var
-- statement:
--   The LLexpr construction uses the eval var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L78-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/LLexpr.lean#L78-L79

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

theorem LLexpr.eval_var (x : Fin n → X) (i : Fin n) : eval x (.var i) = x i := by sorry

attribute [defeq] LLexpr.eval_var
