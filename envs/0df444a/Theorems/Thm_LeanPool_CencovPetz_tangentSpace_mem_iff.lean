-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_tangentSpace_mem_iff
-- name    : LeanPool.CencovPetz.tangentSpace.mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:28.839577+00:00
-- url     : https://prove2.me/theorems/f7465c39-a0a4-4105-9caf-6ac70f7d3dd5
-- title:
--   tangent Space: mem iff
-- statement:
--   The tangent Space construction uses the mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Simplex.lean#L90-L92
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Simplex.lean#L90-L92

module
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
public import Definitions.Def_LeanPool_CencovPetz_Simplex
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
variable {α : Type*} [Fintype α]
open LeanPool.CencovPetz.tangentSpace
variable (α)

theorem LeanPool.CencovPetz.tangentSpace.mem_iff {u : α → ℝ} :
    u ∈ tangentSpace (α := α) ↔ (∑ a, u a) = 0 := by sorry
