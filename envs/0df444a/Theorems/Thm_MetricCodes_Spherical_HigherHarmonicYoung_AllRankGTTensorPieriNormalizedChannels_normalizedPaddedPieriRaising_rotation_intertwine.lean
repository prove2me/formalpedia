-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTensorPieriNormalizedChannels_normalizedPaddedPieriRaising_rotation_intertwine
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTensorPieriNormalizedChannels.normalizedPaddedPieriRaising_rotation_intertwine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:07.830035+00:00
-- url     : https://prove2.me/theorems/480d0f19-bf57-41c1-bc1c-78932b86015f
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTensorPieriNormalizedChannels.normalizedPaddedPieriRaising_rotation_intertwine
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
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTensorPieriNormalizedChannels
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalEdgeRaisingGram
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisAssembly
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTensorPieriNormalizedChannels.normalizedPaddedPieriRaising_rotation_intertwine
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (row : PaddedPieriLowerRow target) (a b : Fin n) :
    (normalizedPaddedPieriRaising hn target hdom row).toLinearMap.comp
        (youngAmbientRotation
          (loweredInternalYoungWeight target row.val) a b) =
      (ClebschRotation.tensorAmbientRotation target a b).comp
        (normalizedPaddedPieriRaising hn target hdom row).toLinearMap := by sorry
