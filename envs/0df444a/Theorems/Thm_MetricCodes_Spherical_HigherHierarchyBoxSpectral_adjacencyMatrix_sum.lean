-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxSpectral_adjacencyMatrix_sum
-- name    : MetricCodes.Spherical.HigherHierarchyBoxSpectral.adjacencyMatrix_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:55.676703+00:00
-- url     : https://prove2.me/theorems/725a0867-2acf-4328-9cf5-c3d87a02dc4f
-- title:
--   MetricCodes.Spherical.HigherHierarchyBoxSpectral.adjacencyMatrix_sum
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

theorem MetricCodes.Spherical.HigherHierarchyBoxSpectral.adjacencyMatrix_sum {r m : ℕ}
    (edge : BoxVertex r m → Fin (r + 1) → ℝ) :
    (∑ v : BoxVertex r m, ∑ w : BoxVertex r m,
      adjacencyMatrix edge v w) =
      2 * ∑ v : BoxVertex r m, ∑ i : Fin (r + 1),
        if (v i).val < m then edge v i else 0 := by sorry
