-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_TangentFin_Bilin_B_symm
-- name    : LeanPool.CencovPetz.TangentFin.Bilin.B_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:30.180167+00:00
-- url     : https://prove2.me/theorems/d934c68d-4268-4d8e-961f-e10f5d001c37
-- title:
--   Bilin: B symm
-- statement:
--   The Bilin construction uses the B symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L152-L153
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L152-L153

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
open LeanPool.CencovPetz.TangentFin.Bilin
open _root_.LeanPool.CencovPetz.TangentFin.Basis
open Perm
variable {n : ℕ} (G : MonotoneMetricFamily) [Nonempty (Fin n)]

theorem LeanPool.CencovPetz.TangentFin.Bilin.B_symm (u v : V n) : B (G := G) (n := n) u v = B (G := G) (n := n) v u := by sorry
