-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchyTrueGridAdjacency_eventually_matrix_irreducible
-- name    : MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency.eventually_matrix_irreducible
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:56.928481+00:00
-- url     : https://prove2.me/theorems/e1da481c-683d-471e-b7e0-cac7b0ea9a01
-- title:
--   MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency.eventually_matrix_irreducible
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
set_option maxHeartbeats 800000
open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyBoxSpectral

theorem MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency.eventually_matrix_irreducible {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b) (ha : ∀ i, 0 < a i)
    (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, (matrix (m := m) a b n).IsIrreducible := by sorry
