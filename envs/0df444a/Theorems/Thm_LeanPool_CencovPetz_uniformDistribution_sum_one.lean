-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_uniformDistribution_sum_one
-- name    : LeanPool.CencovPetz.uniformDistribution_sum_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:29.063575+00:00
-- url     : https://prove2.me/theorems/4b488d59-f92f-405d-83de-4b8f1b2b8d1d
-- title:
--   Cencov Petz: uniform Distribution sum one
-- statement:
--   The uniform distribution sums to `1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Uniform.lean#L46-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Uniform.lean#L46-L48

module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_CencovPetz_Uniform
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u

theorem LeanPool.CencovPetz.uniformDistribution_sum_one {α : Type u} [Fintype α] [Nonempty α] :
    (∑ a : α, uniformDistribution (α := α) a) = 1 := by sorry
