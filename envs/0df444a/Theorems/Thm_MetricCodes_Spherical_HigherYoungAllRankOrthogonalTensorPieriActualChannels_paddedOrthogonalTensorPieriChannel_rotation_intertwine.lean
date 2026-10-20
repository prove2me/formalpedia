-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalTensorPieriActualChannels_paddedOrthogonalTensorPieriChannel_rotation_intertwine
-- name    : MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels.paddedOrthogonalTensorPieriChannel_rotation_intertwine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:07.830035+00:00
-- url     : https://prove2.me/theorems/2f0a8cac-f32d-4aad-8935-2717972f0579
-- title:
--   MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels.paddedOrthogonalTensorPieriChannel_rotation_intertwine
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
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalTensorPieriDimension
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTensorPieriNormalizedChannels
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

theorem MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriActualChannels.paddedOrthogonalTensorPieriChannel_rotation_intertwine
    {r n : ℕ} (hn : 2 * r + 4 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (i : PaddedPieriChannel target) (a b : Fin n) :
    (paddedOrthogonalTensorPieriChannel hn target hdom i).toLinearMap.comp
        (youngAmbientRotation (paddedPieriSource target i) a b) =
      (ClebschRotation.tensorAmbientRotation target a b).comp
        (paddedOrthogonalTensorPieriChannel hn target hdom i).toLinearMap := by sorry
