-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxSpectral_forwardFace_card
-- name    : MetricCodes.Spherical.HigherHierarchyBoxSpectral.forwardFace_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:55.676703+00:00
-- url     : https://prove2.me/theorems/a7e0311f-a23f-4c65-b6f3-dc56fabc7a39
-- title:
--   MetricCodes.Spherical.HigherHierarchyBoxSpectral.forwardFace_card
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
open scoped BigOperators Matrix Topology
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherChannel

theorem MetricCodes.Spherical.HigherHierarchyBoxSpectral.forwardFace_card {r m : ℕ} (i : Fin (r + 1)) :
    ((Finset.univ : Finset (BoxVertex r m)).filter
      (fun v => (v i).val < m)).card = m * (m + 1) ^ r := by sorry
