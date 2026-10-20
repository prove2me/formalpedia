-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_tendsto_linearRowFactor
-- name    : MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_linearRowFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:54.32227+00:00
-- url     : https://prove2.me/theorems/5c7933fd-b1c0-4b49-97e7-9eecea5dc8fc
-- title:
--   MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_linearRowFactor
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
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Nat Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Weyl

theorem MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_linearRowFactor
    (k : ℕ → ℕ) (c : ℕ) {a : ℝ}
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (𝓝 a)) :
    Tendsto
      (fun n : ℕ =>
        (2 * (k n : ℝ) + (n : ℝ) - (c : ℝ)) /
          ((n : ℝ) - (c : ℝ)))
      atTop (𝓝 (2 * a + 1)) := by sorry
