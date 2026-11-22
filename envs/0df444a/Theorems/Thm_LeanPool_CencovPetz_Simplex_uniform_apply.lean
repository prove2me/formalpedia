-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_Simplex_uniform_apply
-- name    : LeanPool.CencovPetz.Simplex.uniform_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:22:21.999034+00:00
-- url     : https://prove2.me/theorems/c8aa18fe-3a79-4fe9-b1c1-0acbe9e1eaf4
-- title:
--   Simplex: uniform apply
-- statement:
--   The Simplex construction uses the uniform apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/UniformSimplex.lean#L41-L43
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/UniformSimplex.lean#L41-L43

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Definitions.Def_LeanPool_CencovPetz_Uniform
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
variable {α : Type*} [Fintype α] [Nonempty α]
open LeanPool.CencovPetz.Simplex

theorem LeanPool.CencovPetz.Simplex.uniform_apply (a : α) :
    (uniform (α := α)).p a = 1 / (Fintype.card α : ℝ) := by sorry

attribute [defeq] LeanPool.CencovPetz.Simplex.uniform_apply
