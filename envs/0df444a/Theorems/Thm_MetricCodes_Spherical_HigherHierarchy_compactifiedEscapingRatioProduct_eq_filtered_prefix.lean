-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedEscapingRatioProduct_eq_filtered_prefix
-- name    : MetricCodes.Spherical.HigherHierarchy.compactifiedEscapingRatioProduct_eq_filtered_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:50.940664+00:00
-- url     : https://prove2.me/theorems/a95ef645-d910-4516-8c93-1c1a3b30b752
-- title:
--   MetricCodes.Spherical.HigherHierarchy.compactifiedEscapingRatioProduct_eq_filtered_prefix
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

theorem MetricCodes.Spherical.HigherHierarchy.compactifiedEscapingRatioProduct_eq_filtered_prefix
    {R k j : ℕ} (hkj : k + j = R) (d : Fin R → ℝ) :
    compactifiedEscapingRatioProduct hkj d =
      ∏ i ∈ Finset.univ.filter (fun i : Fin R => i.val < k), d i := by sorry
