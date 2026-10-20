-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherProjectionInstantiation_mem_codePoints_iff
-- name    : MetricCodes.Spherical.HigherProjectionInstantiation.mem_codePoints_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:54.32227+00:00
-- url     : https://prove2.me/theorems/e35be18b-db04-430c-9d86-ddf22fdd3dab
-- title:
--   MetricCodes.Spherical.HigherProjectionInstantiation.mem_codePoints_iff
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
open scoped BigOperators InnerProductSpace Matrix
open MetricCodes.Spherical.HigherProjectionInstantiation

theorem MetricCodes.Spherical.HigherProjectionInstantiation.mem_codePoints_iff {n : ℕ} {s : ℝ}
    (C : SpherePacking.SphericalCode n s) (x : SpherePoint n) :
    x ∈ codePoints C ↔ x.val ∈ C.points := by sorry
