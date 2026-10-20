-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactified_entropy_sum_eq_residual_sub_logb
-- name    : MetricCodes.Spherical.HigherHierarchy.compactified_entropy_sum_eq_residual_sub_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:49.086537+00:00
-- url     : https://prove2.me/theorems/4113d35e-6172-46fa-9afc-efec6a75690b
-- title:
--   MetricCodes.Spherical.HigherHierarchy.compactified_entropy_sum_eq_residual_sub_logb
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

theorem MetricCodes.Spherical.HigherHierarchy.compactified_entropy_sum_eq_residual_sub_logb
    {r k j q : ℕ} (hkj : k + j = r)
    (A : Fin (r + 1) → ℝ) (B d : Fin r → ℝ)
    (a₀ : Fin (q + 1) → ℝ) (b₀ : Fin q → ℝ) (c : ℝ)
    (hzero : ∀ i : Fin r, A i.castSucc = 0 ↔ i.val < k)
    (hd : ∀ i : Fin r, i.val < k → 0 < d i)
    (hresidualPhi :
      Phi a₀ b₀ =
        Phi (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1))
    (hc : c = ∏ i ∈ Finset.univ.filter
      (fun i : Fin r => i.val < k), d i) :
    (∑ i : Fin r,
      if A i.castSucc = 0 then -Real.logb 2 (d i)
      else MetricCodes.sphericalEntropy ((A i.castSucc)⁻¹ - 1) -
        MetricCodes.sphericalEntropy ((B i)⁻¹ - 1)) +
      MetricCodes.sphericalEntropy ((A (Fin.last r))⁻¹ - 1) =
        Phi a₀ b₀ - Real.logb 2 c := by sorry
