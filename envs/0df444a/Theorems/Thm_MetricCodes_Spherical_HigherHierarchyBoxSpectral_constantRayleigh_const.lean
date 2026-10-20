-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxSpectral_constantRayleigh_const
-- name    : MetricCodes.Spherical.HigherHierarchyBoxSpectral.constantRayleigh_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:55.676703+00:00
-- url     : https://prove2.me/theorems/80939af4-6f13-4bc0-99f7-a4ed9db297ee
-- title:
--   MetricCodes.Spherical.HigherHierarchyBoxSpectral.constantRayleigh_const
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

theorem MetricCodes.Spherical.HigherHierarchyBoxSpectral.constantRayleigh_const {r m : ℕ}
    (weight : Fin (r + 1) → ℝ) :
    constantRayleigh (fun _ : BoxVertex r m => weight) =
      (2 * (m : ℝ) / (m + 1 : ℝ)) *
        ∑ i : Fin (r + 1), weight i := by sorry
