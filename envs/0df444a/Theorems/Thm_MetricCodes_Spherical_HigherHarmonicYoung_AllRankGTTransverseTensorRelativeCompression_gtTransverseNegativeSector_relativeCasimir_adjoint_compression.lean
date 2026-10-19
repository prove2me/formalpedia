-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTensorRelativeCompression_gtTransverseNegativeSector_relativeCasimir_adjoint_compression
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression.gtTransverseNegativeSector_relativeCasimir_adjoint_compression
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:10.573365+00:00
-- url     : https://prove2.me/theorems/23911b19-dd02-4009-af5c-7d7c3c0d5dae
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression.gtTransverseNegativeSector_relativeCasimir_adjoint_compression
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
set_option maxHeartbeats 3000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression.gtTransverseNegativeSector_relativeCasimir_adjoint_compression
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hgram : PositiveGelfandTsetlinFischerGram (n := n)
      lam (raiseWeight mu row) hnu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (gtTransverseTensorEmbedding lam (raiseWeight mu row) hnu hgram).toLinearMap.adjoint
        (gtRelativeCasimir (n := n + 1) lam
          (gtTransverseNegativeSector lam mu row hnu hgram p)) =
      gtStabilizerArrowheadNode (wallShift (n + 1) (r + 1))
        (MetricCodes.Spherical.HigherChannel.stabilizerShift (n + 1) mu)
          (.inr (row, false)) •
          youngClebschRaise (raiseWeight mu row) mu
            (sum_raiseWeight mu row) row p := by sorry
