-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_TangentFin_Bilin_B_dij_dij_eq_half_self
-- name    : LeanPool.CencovPetz.TangentFin.Bilin.B_dij_dij_eq_half_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:51.55283+00:00
-- url     : https://prove2.me/theorems/18d683e0-a742-4338-be97-19b56f1061db
-- title:
--   Bilin: B dij dij eq half self
-- statement:
--   The Bilin construction uses the B dij dij eq half self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L265-L285
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L265-L285

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

theorem LeanPool.CencovPetz.TangentFin.Bilin.B_dij_dij_eq_half_self (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i k) =
      (1 / 2 : ℝ) * B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) := by sorry
