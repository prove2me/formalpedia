-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalTensorPieriDimension_sum_det_updateRow_orthogonalTensorPieriSignedShiftMatrix
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension.sum_det_updateRow_orthogonalTensorPieriSignedShiftMatrix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:07.830035+00:00
-- url     : https://prove2.me/theorems/d9272a11-dbdf-412b-8629-4c51bd2cfc17
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension.sum_det_updateRow_orthogonalTensorPieriSignedShiftMatrix
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
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherWeylAllRankJacobiTrudiWeylEvaluation
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriBoundaryColumn
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriRowFiltering
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension.sum_det_updateRow_orthogonalTensorPieriSignedShiftMatrix
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (hzero : lam (Fin.last r) = 0) :
    (∑ i : Fin (r + 1),
      ((orthogonalJacobiTrudiMatrix n lam).updateRow i
        (orthogonalTensorPieriSignedShiftMatrix n lam i)).det) =
      (n : ℤ) * orthogonalJacobiTrudiDimension n lam := by sorry
