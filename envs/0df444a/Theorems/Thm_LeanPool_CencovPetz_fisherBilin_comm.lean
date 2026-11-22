-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_fisherBilin_comm
-- name    : LeanPool.CencovPetz.fisherBilin.comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:20:30.043033+00:00
-- url     : https://prove2.me/theorems/664addfc-9c07-4404-b95f-9e6b26321320
-- title:
--   fisher Bilin: comm
-- statement:
--   The fisher Bilin construction uses the comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Simplex.lean#L128-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/Simplex.lean#L128-L131

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

theorem LeanPool.CencovPetz.fisherBilin.comm (u v : tangentSpace (α := α)) :
    fisherBilin p u v = fisherBilin p v u := by sorry
