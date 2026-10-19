-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_variationalRate_lowerSemicontinuousOn_Icc
-- name    : MetricCodes.Spherical.HigherHierarchy.variationalRate_lowerSemicontinuousOn_Icc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:52.737619+00:00
-- url     : https://prove2.me/theorems/2fc66457-2b0c-4dd7-8d3c-88f17163e5f9
-- title:
--   MetricCodes.Spherical.HigherHierarchy.variationalRate_lowerSemicontinuousOn_Icc
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
open Set Filter Topology
open scoped Topology

theorem MetricCodes.Spherical.HigherHierarchy.variationalRate_lowerSemicontinuousOn_Icc
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    LowerSemicontinuousOn MetricCodes.Spherical.variationalRate
      (Set.Icc (0 : ℝ) s) := by sorry
