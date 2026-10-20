-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCanonicalPhysicalSignedSpan_canonicalGelfandTsetlinAxisTensor_mem_gtSelectedPhysicalSignedSpan
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCanonicalPhysicalSignedSpan.canonicalGelfandTsetlinAxisTensor_mem_gtSelectedPhysicalSignedSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:09.321996+00:00
-- url     : https://prove2.me/theorems/6d763191-51e3-49c5-b9d0-18190fdf45ae
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCanonicalPhysicalSignedSpan.canonicalGelfandTsetlinAxisTensor_mem_gtSelectedPhysicalSignedSpan
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
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCanonicalPhysicalSignedSpan
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalChannelRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseOrthogonalCompleteness
open MetricCodes.Spherical.HigherRepresentationGraph

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCanonicalPhysicalSignedSpan.canonicalGelfandTsetlinAxisTensor_mem_gtSelectedPhysicalSignedSpan
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces low mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) low mu h)
    (hfinite : FiniteInterlacing (n + 1) low mu)
    (hdom : Antitone low) (row : Fin (r + 2))
    (hhigh : Antitone (raiseWeight low row))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    canonicalGelfandTsetlinAxisTensor low mu h hgram p ∈
      gtSelectedPhysicalSignedSpan (n := n + 1) low row := by sorry
