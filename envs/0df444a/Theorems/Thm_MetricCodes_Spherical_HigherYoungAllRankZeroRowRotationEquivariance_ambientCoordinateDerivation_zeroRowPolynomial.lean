-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankZeroRowRotationEquivariance_ambientCoordinateDerivation_zeroRowPolynomial
-- name    : MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance.ambientCoordinateDerivation_zeroRowPolynomial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:01.713242+00:00
-- url     : https://prove2.me/theorems/61d2ccc8-b9cb-4d2e-80db-8e257aa2c447
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance.ambientCoordinateDerivation_zeroRowPolynomial
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
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance.ambientCoordinateDerivation_zeroRowPolynomial
    {r n : ℕ} (a b : Fin n) (p : PolynomialSpace r n) :
    ambientCoordinateDerivation (r := r + 1) a b
        (zeroRowPolynomial n p) =
      zeroRowPolynomial n
        (ambientCoordinateDerivation (r := r) a b p) := by sorry
