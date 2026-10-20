-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_drop_second_of_collision
-- name    : MetricCodes.Spherical.HigherHierarchy.Phi_drop_second_of_collision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:49.086537+00:00
-- url     : https://prove2.me/theorems/610d90f7-bb4f-4295-bfe7-708f5431448a
-- title:
--   MetricCodes.Spherical.HigherHierarchy.Phi_drop_second_of_collision
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
open scoped BigOperators

theorem MetricCodes.Spherical.HigherHierarchy.Phi_drop_second_of_collision {r : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hcollision : b 0 = a (1 : Fin (r + 2))) :
    Phi a b =
      Phi (Fin.cons (a 0) (Fin.tail (Fin.tail a))) (Fin.tail b) := by sorry
