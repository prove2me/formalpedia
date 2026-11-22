-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_TangentFin_Bilin_B_dij_dij_eq_zero_of_disjoint
-- name    : LeanPool.CencovPetz.TangentFin.Bilin.B_dij_dij_eq_zero_of_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:02.914091+00:00
-- url     : https://prove2.me/theorems/3d6f7951-ded7-4183-9262-85402eb02d65
-- title:
--   Bilin: B dij dij eq zero of disjoint
-- statement:
--   The Bilin construction uses the B dij dij eq zero of disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L168-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L168-L194

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

theorem LeanPool.CencovPetz.TangentFin.Bilin.B_dij_dij_eq_zero_of_disjoint (i j k l : Fin n)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) k l) = 0 := by sorry
