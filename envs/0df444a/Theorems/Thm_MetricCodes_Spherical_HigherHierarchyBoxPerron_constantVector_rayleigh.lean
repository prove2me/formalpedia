-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxPerron_constantVector_rayleigh
-- name    : MetricCodes.Spherical.HigherHierarchyBoxPerron.constantVector_rayleigh
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:56.928481+00:00
-- url     : https://prove2.me/theorems/155fd6e6-8202-4b8d-a15c-12ace1f7e20e
-- title:
--   MetricCodes.Spherical.HigherHierarchyBoxPerron.constantVector_rayleigh
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
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherHierarchyBoxPerron
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyBoxSpectral

theorem MetricCodes.Spherical.HigherHierarchyBoxPerron.constantVector_rayleigh {r m : ℕ}
    (edge : BoxVertex r m → Fin (r + 1) → ℝ) :
    HigherHierarchyFinitePerron.rayleigh
      (adjacencyMatrix edge) (constantVector r m) =
      constantRayleigh edge := by sorry
