-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_rateSet_subset_hierarchyRateSet
-- name    : MetricCodes.Spherical.HigherHierarchy.rateSet_subset_hierarchyRateSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:42.425795+00:00
-- url     : https://prove2.me/theorems/b8a4d15b-5a31-4610-8f71-1b0250d7e0f8
-- title:
--   MetricCodes.Spherical.HigherHierarchy.rateSet_subset_hierarchyRateSet
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

theorem MetricCodes.Spherical.HigherHierarchy.rateSet_subset_hierarchyRateSet (s : ℝ) :
    MetricCodes.Spherical.rateSet s ⊆ hierarchyRateSet s := by sorry
