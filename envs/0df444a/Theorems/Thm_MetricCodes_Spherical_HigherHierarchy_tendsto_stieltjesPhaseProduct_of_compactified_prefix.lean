-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_stieltjesPhaseProduct_of_compactified_prefix
-- name    : MetricCodes.Spherical.HigherHierarchy.tendsto_stieltjesPhaseProduct_of_compactified_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:50.940664+00:00
-- url     : https://prove2.me/theorems/8f6d7986-558a-44a4-897e-5cd51a0f1223
-- title:
--   MetricCodes.Spherical.HigherHierarchy.tendsto_stieltjesPhaseProduct_of_compactified_prefix
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology
open scoped BigOperators Topology

theorem MetricCodes.Spherical.HigherHierarchy.tendsto_stieltjesPhaseProduct_of_compactified_prefix
    {k r q : ℕ}
    (a : ℕ → Fin (k + r + 1) → ℝ)
    (b : ℕ → Fin (k + r) → ℝ)
    (A : Fin (k + r + 1) → ℝ)
    (B d : Fin (k + r) → ℝ)
    (A' : Fin (q + 1) → ℝ) (B' : Fin q → ℝ)
    (h : ∀ n, Interlacing (a n) (b n))
    (hA : ∀ i, A i ∈ Set.Icc (0 : ℝ) 1)
    (ha : ∀ i,
      Tendsto (fun n => compactifiedHierarchyCoordinate (a n i))
        atTop (𝓝 (A i)))
    (hb : ∀ i,
      Tendsto (fun n => compactifiedHierarchyCoordinate (b n i))
        atTop (𝓝 (B i)))
    (hd : ∀ i,
      Tendsto (fun n => b n i / a n i.castSucc)
        atTop (𝓝 (d i)))
    (hzero : ∀ i : Fin k, A (i.castAdd (r + 1)) = 0)
    (hpositiveA : ∀ i : Fin (r + 1), 0 < A (i.natAdd k))
    (hpositiveB : ∀ i : Fin r, 0 < B (i.natAdd k))
    (hratio : ∀ t : ℝ, 0 < t →
      hierarchyStieltjesRatio
          (fun i : Fin (r + 1) => (A (i.natAdd k))⁻¹ - 1)
          (fun i : Fin r => (B (i.natAdd k))⁻¹ - 1) t =
        hierarchyStieltjesRatio A' B' t)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
      atTop
      (𝓝 ((∏ i : Fin k, d (i.castAdd r) ^ 2) *
        stieltjesPhaseProduct A' B' t)) := by sorry
