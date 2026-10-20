-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn_det_updateCol_last_of_lastRow_delta
-- name    : MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn.det_updateCol_last_of_lastRow_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:07.830035+00:00
-- url     : https://prove2.me/theorems/0f841365-ab10-47ed-8352-ec5c604ff1dd
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn.det_updateCol_last_of_lastRow_delta
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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn

theorem MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn.det_updateCol_last_of_lastRow_delta
    {R : Type*} [CommRing R] {r : ℕ}
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (v : Fin (r + 1) → R)
    (hrow : ∀ j, M (Fin.last r) j = if j = Fin.last r then 1 else 0) :
    (M.updateCol (Fin.last r) v).det = v (Fin.last r) * M.det := by sorry
