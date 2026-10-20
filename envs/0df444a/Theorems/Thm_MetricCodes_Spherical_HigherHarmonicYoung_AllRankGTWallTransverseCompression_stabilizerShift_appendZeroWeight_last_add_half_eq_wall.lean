-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_stabilizerShift_appendZeroWeight_last_add_half_eq_wall
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression.stabilizerShift_appendZeroWeight_last_add_half_eq_wall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:12.645026+00:00
-- url     : https://prove2.me/theorems/04e790b6-2b09-4e0d-8861-fd6810e7822d
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression.stabilizerShift_appendZeroWeight_last_add_half_eq_wall
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
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression.stabilizerShift_appendZeroWeight_last_add_half_eq_wall
    {r n : ℕ} (mu : Fin (r + 1) → ℕ) :
    stabilizerShift (n + 1) (appendZeroWeight mu) (Fin.last (r + 1)) +
        (1 / 2 : ℝ) = wallShift (n + 1) (r + 1) := by sorry
