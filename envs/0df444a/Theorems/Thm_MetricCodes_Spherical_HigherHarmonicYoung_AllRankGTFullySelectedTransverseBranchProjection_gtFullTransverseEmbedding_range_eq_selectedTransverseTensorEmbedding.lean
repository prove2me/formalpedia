-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTFullySelectedTransverseBranchProjection_gtFullTransverseEmbedding_range_eq_selectedTransverseTensorEmbedding
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullySelectedTransverseBranchProjection.gtFullTransverseEmbedding_range_eq_selectedTransverseTensorEmbedding
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:14.457341+00:00
-- url     : https://prove2.me/theorems/3fabce5f-4cef-4685-a609-23ebb91aba72
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullySelectedTransverseBranchProjection.gtFullTransverseEmbedding_range_eq_selectedTransverseTensorEmbedding
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
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullySelectedTransverseBranchProjection
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTFullySelectedTransverseBranchProjection.gtFullTransverseEmbedding_range_eq_selectedTransverseTensorEmbedding
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (tau : Fin (r + 1) → ℕ) (h : Interlaces lam tau)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hdom : Antitone lam)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam tau h) :
    LinearMap.range
        (gtFullTransverseEmbedding lam hn
          (fullBranchOfInterlaces tau h)).toLinearMap =
      LinearMap.range
        (gtTransverseTensorEmbedding lam tau h hgram).toLinearMap := by sorry
