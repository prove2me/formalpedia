-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_add
-- name    : LeanPool.CencovPetz.TangentFin.Basis.dij_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:26.31244+00:00
-- url     : https://prove2.me/theorems/1f271806-cb58-4c74-978e-3c46edec42f1
-- title:
--   Basis: dij add
-- statement:
--   The Basis construction uses the dij add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L72-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L72-L74

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

theorem LeanPool.CencovPetz.TangentFin.Basis.dij_add (i j k : Fin n) : dij (n := n) i k = dij (n := n) i j + dij (n := n) j k := by sorry
