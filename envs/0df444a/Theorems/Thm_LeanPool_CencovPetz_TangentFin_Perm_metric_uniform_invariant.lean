-- Prove2me | Theorems.Thm_LeanPool_CencovPetz_TangentFin_Perm_metric_uniform_invariant
-- name    : LeanPool.CencovPetz.TangentFin.Perm.metric_uniform_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:48.603467+00:00
-- url     : https://prove2.me/theorems/4a1184c0-b384-42d8-a1e4-1be7f8789ab7
-- title:
--   Perm: metric uniform invariant
-- statement:
--   The Perm construction uses the metric uniform invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L129-L137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CencovPetz/PermutationInvariantBilinForm.lean#L129-L137

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

theorem LeanPool.CencovPetz.TangentFin.Perm.metric_uniform_invariant {n : ℕ} (G : MonotoneMetricFamily) [Nonempty (Fin n)]
    (σ : Equiv.Perm (Fin n)) (u v : V n) :
    G.g (α := Fin n) (Simplex.uniform (α := Fin n))
        ((κ (n := n) σ).tangentPushforward u) ((κ (n := n) σ).tangentPushforward v)
      = G.g (α := Fin n) (Simplex.uniform (α := Fin n)) u v := by sorry
