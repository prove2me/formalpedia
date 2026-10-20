-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_boundaryQuadratic_eq_sq_mul_normalized
-- name    : MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.boundaryQuadratic_eq_sq_mul_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:42.425795+00:00
-- url     : https://prove2.me/theorems/5a60d9f8-bfb8-4ecb-baa2-43704cf828fa
-- title:
--   MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.boundaryQuadratic_eq_sq_mul_normalized
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
open Filter
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy

theorem MetricCodes.Spherical.HigherHierarchy.CompactificationEntropy.boundaryQuadratic_eq_sq_mul_normalized
    {s a : ℝ} (ha : 0 < a) :
    MetricCodes.Spherical.boundaryQuadratic s a =
      a ^ 2 * normalizedBoundaryQuadratic s a⁻¹ := by sorry
