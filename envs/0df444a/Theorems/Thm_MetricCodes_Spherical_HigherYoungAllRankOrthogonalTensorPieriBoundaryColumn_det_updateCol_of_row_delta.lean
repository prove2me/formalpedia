-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn_det_updateCol_of_row_delta
-- name    : MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn.det_updateCol_of_row_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:07.830035+00:00
-- url     : https://prove2.me/theorems/a48b4566-e904-4a1b-bb20-64790a5a6295
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn.det_updateCol_of_row_delta
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

theorem MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn.det_updateCol_of_row_delta
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (i : ι) (v : ι → R)
    (hrow : ∀ j, M i j = if j = i then 1 else 0) :
    (M.updateCol i v).det = v i * M.det := by sorry
