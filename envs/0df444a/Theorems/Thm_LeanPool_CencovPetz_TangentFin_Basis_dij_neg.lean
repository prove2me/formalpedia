-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_neg
-- name    : LeanPool.CencovPetz.TangentFin.Basis.dij_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:27.559563+00:00
-- url     : https://prove2.me/theorems/4619d3f9-4fe1-4a7f-a108-a136700790bd
-- title:
--   Basis: dij neg
-- statement:
--   The Basis construction uses the dij neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L68-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L68-L70

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

theorem LeanPool.CencovPetz.TangentFin.Basis.dij_neg (i j : Fin n) : dij (n := n) i j = -dij (n := n) j i := by sorry
