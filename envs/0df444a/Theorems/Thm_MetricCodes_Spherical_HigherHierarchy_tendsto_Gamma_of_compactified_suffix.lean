-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_Gamma_of_compactified_suffix
-- name    : MetricCodes.Spherical.HigherHierarchy.tendsto_Gamma_of_compactified_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:50.940664+00:00
-- url     : https://prove2.me/theorems/b5f942cf-0270-4558-8880-5fc5a925f5f1
-- title:
--   MetricCodes.Spherical.HigherHierarchy.tendsto_Gamma_of_compactified_suffix
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

theorem MetricCodes.Spherical.HigherHierarchy.tendsto_Gamma_of_compactified_suffix
    {R k j q : ℕ} (hkj : k + j = R)
    (a : ℕ → Fin (R + 1) → ℝ)
    (b : ℕ → Fin R → ℝ)
    (A : Fin (R + 1) → ℝ)
    (B d : Fin R → ℝ)
    (A' : Fin (q + 1) → ℝ) (B' : Fin q → ℝ)
    (c : ℝ)
    (h : ∀ n, Interlacing (a n) (b n))
    (hAB : Interlacing A' B')
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
    (hzero : ∀ i : Fin R, i.val < k → A i.castSucc = 0)
    (hpositiveA : ∀ i,
      0 < compactifiedAmbientSuffix hkj A i)
    (hpositiveB : ∀ i,
      0 < compactifiedStabilizerSuffix hkj B i)
    (hratio : ∀ t : ℝ, 0 < t →
      hierarchyStieltjesRatio
          (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) t =
        hierarchyStieltjesRatio A' B' t)
    (hc : c = ∏ i ∈ Finset.univ.filter
      (fun i : Fin R => i.val < k), d i) :
    Tendsto (fun n => Gamma (a n) (b n))
      atTop (𝓝 (((1 - c ^ 2) / 2) + c ^ 2 * Gamma A' B')) := by sorry
