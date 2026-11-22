-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_sum_e
-- name    : LeanPool.CencovPetz.TangentFin.Basis.sum_e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:59.615612+00:00
-- url     : https://prove2.me/theorems/5e9a5e77-7b89-41da-a6c2-6084c7f47a19
-- title:
--   Basis: sum e
-- statement:
--   The Basis construction uses the sum e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L45-L47
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L45-L47

module
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariantBilinForm
set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {n : ℕ}
open LeanPool.CencovPetz.TangentFin
open LeanPool.CencovPetz.TangentFin.Basis

theorem LeanPool.CencovPetz.TangentFin.Basis.sum_e (i : Fin n) : (∑ k : Fin n, e (n := n) i k) = 1 := by sorry
