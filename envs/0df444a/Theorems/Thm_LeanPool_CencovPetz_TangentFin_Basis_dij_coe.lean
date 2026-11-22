-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_coe
-- name    : LeanPool.CencovPetz.TangentFin.Basis.dij_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:16.036635+00:00
-- url     : https://prove2.me/theorems/46f4172e-aead-4ca0-96b7-06960628dd86
-- title:
--   Basis: dij coe
-- statement:
--   The Basis construction uses the dij coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L60-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L60-L62

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

theorem LeanPool.CencovPetz.TangentFin.Basis.dij_coe (i j : Fin n) (k : Fin n) :
    (dij (n := n) i j : Fin n → ℝ) k = e (n := n) i k - e (n := n) j k := by sorry

attribute [defeq] LeanPool.CencovPetz.TangentFin.Basis.dij_coe
