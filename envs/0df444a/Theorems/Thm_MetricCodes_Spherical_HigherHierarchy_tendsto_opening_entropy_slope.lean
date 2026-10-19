-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_opening_entropy_slope
-- name    : MetricCodes.Spherical.HigherHierarchy.tendsto_opening_entropy_slope
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:40.58935+00:00
-- url     : https://prove2.me/theorems/196d23f9-0475-4d0a-a510-43f35a25fc8b
-- title:
--   MetricCodes.Spherical.HigherHierarchy.tendsto_opening_entropy_slope
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

theorem MetricCodes.Spherical.HigherHierarchy.tendsto_opening_entropy_slope {a η : ℝ}
    (ha : 0 < a) :
    Tendsto
      (fun t : ℝ =>
        (MetricCodes.sphericalEntropy (a - η * t) -
          MetricCodes.sphericalEntropy a +
          MetricCodes.sphericalEntropy (t ^ 2)) / t)
      (𝓝[>] 0)
      (nhds (-(η * Real.logb 2 ((1 + a) / a)))) := by sorry
