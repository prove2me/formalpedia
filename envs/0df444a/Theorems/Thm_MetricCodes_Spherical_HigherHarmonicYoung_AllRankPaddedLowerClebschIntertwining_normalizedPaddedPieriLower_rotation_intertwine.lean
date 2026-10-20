-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankPaddedLowerClebschIntertwining_normalizedPaddedPieriLower_rotation_intertwine
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining.normalizedPaddedPieriLower_rotation_intertwine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:06.385168+00:00
-- url     : https://prove2.me/theorems/eec92955-f73a-4dd9-bb3c-20021e94f8a2
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining.normalizedPaddedPieriLower_rotation_intertwine
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
set_option maxHeartbeats 1800000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungArbitraryRowLoweringProjectedAxisWitness
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining.normalizedPaddedPieriLower_rotation_intertwine
    {r n : ℕ} (target : Fin (r + 1) → ℕ)
    (hdominant : Antitone target)
    (row : Fin (r + 1))
    (hsource : Antitone (raiseWeight target row))
    (i j : Fin n) :
    (normalizedPaddedPieriLower (n := n)
      target hdominant row hsource).toLinearMap.comp
        (youngAmbientRotation (raiseWeight target row) i j) =
      (ClebschRotation.tensorAmbientRotation target i j).comp
        (normalizedPaddedPieriLower (n := n)
          target hdominant row hsource).toLinearMap := by sorry
