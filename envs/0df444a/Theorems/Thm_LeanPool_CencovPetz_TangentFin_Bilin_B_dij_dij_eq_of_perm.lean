-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_TangentFin_Bilin_B_dij_dij_eq_of_perm
-- name    : LeanPool.CencovPetz.TangentFin.Bilin.B_dij_dij_eq_of_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:44.068843+00:00
-- url     : https://prove2.me/theorems/04250508-855b-4704-97a4-957971dc26f4
-- title:
--   Bilin: B dij dij eq of perm
-- statement:
--   The Bilin construction uses the B dij dij eq of perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L161-L166
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L161-L166

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

theorem LeanPool.CencovPetz.TangentFin.Bilin.B_dij_dij_eq_of_perm (σ : Equiv.Perm (Fin n)) (i j k l : Fin n) :
    B (G := G) (n := n) (dij (n := n) (σ i) (σ j)) (dij (n := n) (σ k) (σ l))
      = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) k l) := by sorry
