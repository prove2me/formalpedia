-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
-- name    : LeanPool.CencovPetz.fisherBilin.apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:30.432956+00:00
-- url     : https://prove2.me/theorems/bf7d7232-b71b-4205-9466-00ff40eecc5b
-- title:
--   fisher Bilin: apply
-- statement:
--   The fisher Bilin construction uses the apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Simplex.lean#L124-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Simplex.lean#L124-L126

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
open LeanPool.CencovPetz.fisherBilin
variable (p : Simplex α)

theorem LeanPool.CencovPetz.fisherBilin.apply (u v : tangentSpace (α := α)) :
    fisherBilin p u v = ∑ a, ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a := by sorry

attribute [defeq] LeanPool.CencovPetz.fisherBilin.apply
