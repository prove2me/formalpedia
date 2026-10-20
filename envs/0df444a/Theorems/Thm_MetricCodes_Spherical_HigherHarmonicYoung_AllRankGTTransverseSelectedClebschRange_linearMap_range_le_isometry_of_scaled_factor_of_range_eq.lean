-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseSelectedClebschRange_linearMap_range_le_isometry_of_scaled_factor_of_range_eq
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSelectedClebschRange.linearMap_range_le_isometry_of_scaled_factor_of_range_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:15.843669+00:00
-- url     : https://prove2.me/theorems/1f5fe3af-eddf-4b9f-bd55-b890c1422947
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSelectedClebschRange.linearMap_range_le_isometry_of_scaled_factor_of_range_eq
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
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSelectedClebschRange
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartHighest
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankZeroRowTensorCasimirConjugacy
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungAllRankGTAppendedRowLegality
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseSelectedClebschRange.linearMap_range_le_isometry_of_scaled_factor_of_range_eq
    {W X Y Z : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (F : X →ₗᵢ[ℝ] Y) (E : W →ₗᵢ[ℝ] Y)
    (B : Z →ₗ[ℝ] Y) (C : Z →ₗ[ℝ] W) (phase : ℝ)
    (hrange : LinearMap.range F.toLinearMap =
      LinearMap.range E.toLinearMap)
    (hfactor : B = phase • E.toLinearMap.comp C) :
    LinearMap.range B ≤ LinearMap.range F.toLinearMap := by sorry
