-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTUnconditionalCharacteristicMinor_isometricSector_operator_column_of_mem_axis_sector
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor.isometricSector_operator_column_of_mem_axis_sector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:15.843669+00:00
-- url     : https://prove2.me/theorems/8a8ae9e9-edc0-44f1-97af-ed32b94fc416
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor.isometricSector_operator_column_of_mem_axis_sector
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
set_option maxHeartbeats 6000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentWallCharacteristicFactor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCharacteristicMinorOfValidRoots
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseCharacteristicAnnihilation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseSector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedWallCharacteristicAnnihilation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPresentWallSignedNodeSeparation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalWallAdditiveColumn
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCrossBlock
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseEigenNodeSeparation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseRetainedTwoBlockClosure
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseMinorRoots
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseSectorFamily
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTUnconditionalCharacteristicMinor.isometricSector_operator_column_of_mem_axis_sector
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ H]
    (A B : V →ₗᵢ[ℝ] H) (T : Module.End ℝ H) (d : ℝ)
    (horth : A.toLinearMap.adjoint.comp B.toLinearMap = 0)
    (hdiag : B.toLinearMap.adjoint.comp
      (T.comp B.toLinearMap) = d • LinearMap.id)
    (hclosed : ∀ p : V,
      T (B p) ∈ LinearMap.range A.toLinearMap ⊔
        LinearMap.range B.toLinearMap) :
    T.comp B.toLinearMap = d • B.toLinearMap +
      A.toLinearMap.comp
        (A.toLinearMap.adjoint.comp (T.comp B.toLinearMap)) := by sorry
