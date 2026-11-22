-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_fisherBilin_pos
-- name    : LeanPool.CencovPetz.fisherBilin.pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:26.796994+00:00
-- url     : https://prove2.me/theorems/1d58820e-e5e1-4acc-a5c4-21f0e07f331b
-- title:
--   fisher Bilin: pos
-- statement:
--   The fisher Bilin construction uses the pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Simplex.lean#L133-L167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Simplex.lean#L133-L167

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

theorem LeanPool.CencovPetz.fisherBilin.pos (u : tangentSpace (α := α)) (hu : u ≠ 0) :
    0 < fisherBilin p u u := by sorry
