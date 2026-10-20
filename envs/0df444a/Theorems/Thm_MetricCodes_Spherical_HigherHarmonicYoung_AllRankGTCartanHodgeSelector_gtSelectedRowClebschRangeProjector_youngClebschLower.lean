-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCartanHodgeSelector_gtSelectedRowClebschRangeProjector_youngClebschLower
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector.gtSelectedRowClebschRangeProjector_youngClebschLower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:06.385168+00:00
-- url     : https://prove2.me/theorems/b22674d1-9734-4dac-bda2-c2949d92f9bb
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector.gtSelectedRowClebschRangeProjector_youngClebschLower
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
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 700000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowBaseAxisChannel
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.UniversalBGGRootComplex
open MetricCodes.Spherical.HigherYoungArbitraryRowLoweringProjectedAxisWitness
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.HigherRepresentationGraph

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector.gtSelectedRowClebschRangeProjector_youngClebschLower
    {r n : ℕ} (low : Fin (r + 1) → ℕ)
    (hdom : Antitone low) (row : Fin (r + 1))
    (hhigh : Antitone (raiseWeight low row))
    (p : HarmonicYoungSpace (n := n) (raiseWeight low row)) :
    gtSelectedRowClebschRangeProjector (n := n) low row
        (youngClebschLower low (raiseWeight low row)
          (sum_raiseWeight low row) row p) =
      youngClebschLower low (raiseWeight low row)
        (sum_raiseWeight low row) row p := by sorry
