-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTFullTransverseSameSignatureRow_tensor_mapIsometry_range_eq_of_second_range_eq
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow.tensor_mapIsometry_range_eq_of_second_range_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:14.457341+00:00
-- url     : https://prove2.me/theorems/cbc8aaed-0d7d-4f95-8227-9dd99fa41e4c
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow.tensor_mapIsometry_range_eq_of_second_range_eq
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
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullTransverseSameSignatureRow.tensor_mapIsometry_range_eq_of_second_range_eq
    {E F X Y Z : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (e : E →ₗᵢ[ℝ] F) (g : X →ₗᵢ[ℝ] Z) (h : Y →ₗᵢ[ℝ] Z)
    (heq : LinearMap.range g.toLinearMap = LinearMap.range h.toLinearMap) :
    LinearMap.range (TensorProduct.mapIsometry e g).toLinearMap =
      LinearMap.range (TensorProduct.mapIsometry e h).toLinearMap := by sorry
