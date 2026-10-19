-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_forward_entropy_sum_eq_Phi_suffix_sub_logb_escaping_product
-- name    : MetricCodes.Spherical.HigherHierarchy.forward_entropy_sum_eq_Phi_suffix_sub_logb_escaping_product
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:49.086537+00:00
-- url     : https://prove2.me/theorems/5b0729eb-f51c-4a0c-baf2-87b1579347d9
-- title:
--   MetricCodes.Spherical.HigherHierarchy.forward_entropy_sum_eq_Phi_suffix_sub_logb_escaping_product
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
open scoped BigOperators

theorem MetricCodes.Spherical.HigherHierarchy.forward_entropy_sum_eq_Phi_suffix_sub_logb_escaping_product
    {r k j : ℕ} (hkj : k + j = r)
    (A : Fin (r + 1) → ℝ) (B d : Fin r → ℝ)
    (hzero : ∀ i : Fin r, A i.castSucc = 0 ↔ i.val < k)
    (hd : ∀ i : Fin r, i.val < k → 0 < d i) :
    (∑ i : Fin r,
      if A i.castSucc = 0 then -Real.logb 2 (d i)
      else MetricCodes.sphericalEntropy ((A i.castSucc)⁻¹ - 1) -
        MetricCodes.sphericalEntropy ((B i)⁻¹ - 1)) +
      MetricCodes.sphericalEntropy ((A (Fin.last r))⁻¹ - 1) =
        Phi (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) -
          Real.logb 2 (compactifiedEscapingRatioProduct hkj d) := by sorry
