-- Prove2me | Theorems.Thm_MetricCodes_spherical_dist_sq
-- name    : MetricCodes.spherical_dist_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:35.827193+00:00
-- url     : https://prove2.me/theorems/ec09da79-7507-4617-8f7c-d7470fe8176a
-- title:
--   MetricCodes.spherical_dist_sq
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
noncomputable section
open scoped BigOperators InnerProductSpace
open MetricCodes

theorem MetricCodes.spherical_dist_sq {n : ℕ} (x y : Sphere n) :
    ‖(x : Ambient n) - (y : Ambient n)‖ ^ 2 =
      2 * (1 - sphericalInner x y) := by sorry
