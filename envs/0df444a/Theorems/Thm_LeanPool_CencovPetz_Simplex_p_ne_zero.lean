-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_Simplex_p_ne_zero
-- name    : LeanPool.CencovPetz.Simplex.p_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:33.064618+00:00
-- url     : https://prove2.me/theorems/0e03c8f9-7cb7-4245-a60c-867d0b362ae3
-- title:
--   Simplex: p ne zero
-- statement:
--   The Simplex construction uses the p ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Simplex.lean#L61-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Simplex.lean#L61-L62

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
open LeanPool.CencovPetz.Simplex
variable (p : Simplex α)

theorem LeanPool.CencovPetz.Simplex.p_ne_zero (a : α) : p.p a ≠ 0 := by sorry
