-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriCoefficient_orthogonalTensorPieriCoefficient_raise_row
-- name    : MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient.orthogonalTensorPieriCoefficient_raise_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:06.385168+00:00
-- url     : https://prove2.me/theorems/f3c57970-5dde-4e5f-8433-15a1696f2246
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient.orthogonalTensorPieriCoefficient_raise_row
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
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
open MetricCodes.Spherical.HigherWeylBinomialDeterminant

theorem MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient.orthogonalTensorPieriCoefficient_raise_row
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) :
    orthogonalJacobiTrudiMatrix n
        (Function.update lam i (lam i + 1)) i j =
      orthogonalTensorPieriCoefficient n
        (((lam i : ℤ) - (i.val : ℤ)) + 1) (j.val : ℤ) := by sorry
