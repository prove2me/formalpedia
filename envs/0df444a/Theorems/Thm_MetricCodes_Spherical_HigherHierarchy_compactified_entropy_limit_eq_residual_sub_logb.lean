-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactified_entropy_limit_eq_residual_sub_logb
-- name    : MetricCodes.Spherical.HigherHierarchy.compactified_entropy_limit_eq_residual_sub_logb
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:49.086537+00:00
-- url     : https://prove2.me/theorems/45ac7778-a9bf-403f-abdc-5e7e8e41b0ce
-- title:
--   MetricCodes.Spherical.HigherHierarchy.compactified_entropy_limit_eq_residual_sub_logb
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
open Filter Topology
open scoped BigOperators Topology

theorem MetricCodes.Spherical.HigherHierarchy.compactified_entropy_limit_eq_residual_sub_logb
    {r k j q : ℕ} (hkj : k + j = r)
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B d : Fin r → ℝ}
    {φ : ℕ → ℕ} {C L c : ℝ}
    (a₀ : Fin (q + 1) → ℝ) (b₀ : Fin q → ℝ)
    (hinter : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C)
    (hA : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (a (φ n) i))
      atTop (nhds (A i)))
    (hB : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
      atTop (nhds (B i)))
    (hAnonneg : ∀ i, 0 ≤ A i)
    (hBnonneg : ∀ i, 0 ≤ B i)
    (hlast : 0 < A (Fin.last r))
    (hratio : ∀ i, Tendsto
      (fun n => b (φ n) i / a (φ n) i.castSucc)
      atTop (nhds (d i)))
    (hzero : ∀ i : Fin r, A i.castSucc = 0 ↔ i.val < k)
    (hd : ∀ i : Fin r, i.val < k → 0 < d i)
    (hlimit : Tendsto (fun n => Phi (a (φ n)) (b (φ n)))
      atTop (nhds L))
    (hresidualPhi :
      Phi a₀ b₀ =
        Phi (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1))
    (hc : c = ∏ i ∈ Finset.univ.filter
      (fun i : Fin r => i.val < k), d i) :
    L = Phi a₀ b₀ - Real.logb 2 c := by sorry
