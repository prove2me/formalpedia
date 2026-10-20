-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTNormalizedTransverseRotationIntertwining_gtTransverseNegativeSector_rotation_intertwine
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining.gtTransverseNegativeSector_rotation_intertwine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:12.645026+00:00
-- url     : https://prove2.me/theorems/9fa4c7b9-082f-4b46-bc34-6b35ab05a90a
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining.gtTransverseNegativeSector_rotation_intertwine
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
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseWignerEckartPhase
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedTransverseRotationIntertwining.gtTransverseNegativeSector_rotation_intertwine
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hnu : Interlaces lam (raiseWeight mu row))
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam (raiseWeight mu row) hnu)
    (a b : Fin n) :
    (gtTransverseNegativeSector lam mu row hnu hnuGram).comp
        (youngAmbientRotation mu a b) =
      (tensorAmbientRotation lam a.castSucc b.castSucc).comp
        (gtTransverseNegativeSector lam mu row hnu hnuGram) := by sorry
