-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_sum_neg_logb_eq_neg_logb_compactifiedEscapingRatioProduct
-- name    : MetricCodes.Spherical.HigherHierarchy.sum_neg_logb_eq_neg_logb_compactifiedEscapingRatioProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:49.086537+00:00
-- url     : https://prove2.me/theorems/a562e6b2-ffd6-41a4-96a0-c502504b3eb6
-- title:
--   MetricCodes.Spherical.HigherHierarchy.sum_neg_logb_eq_neg_logb_compactifiedEscapingRatioProduct
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

theorem MetricCodes.Spherical.HigherHierarchy.sum_neg_logb_eq_neg_logb_compactifiedEscapingRatioProduct
    {r k j : ℕ} (hkj : k + j = r) (d : Fin r → ℝ)
    (hd : ∀ i : Fin r, i.val < k → 0 < d i) :
    (∑ i : Fin k, -Real.logb 2 (d ⟨i.val, by omega⟩)) =
      -Real.logb 2 (compactifiedEscapingRatioProduct hkj d) := by sorry
