-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_TangentFin_Perm_e_apply_symm
-- name    : LeanPool.CencovPetz.TangentFin.Perm.e_apply_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:32.661001+00:00
-- url     : https://prove2.me/theorems/2abc6401-8c83-4fdf-85b1-b1d92a5bdc53
-- title:
--   Perm: e apply symm
-- statement:
--   The Perm construction uses the e apply symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L100-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L100-L112

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
open LeanPool.CencovPetz.TangentFin.Perm
open _root_.LeanPool.CencovPetz.TangentFin.Basis

theorem LeanPool.CencovPetz.TangentFin.Perm.e_apply_symm (σ : Equiv.Perm (Fin n)) (i k : Fin n) :
    e (n := n) i (σ.symm k) = e (n := n) (σ i) k := by sorry
