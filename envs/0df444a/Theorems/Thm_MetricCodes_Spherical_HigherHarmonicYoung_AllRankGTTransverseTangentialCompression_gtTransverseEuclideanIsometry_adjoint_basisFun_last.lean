-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTangentialCompression_gtTransverseEuclideanIsometry_adjoint_basisFun_last
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression.gtTransverseEuclideanIsometry_adjoint_basisFun_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:10.573365+00:00
-- url     : https://prove2.me/theorems/714e967a-d58a-49a5-b910-172c5d8ebd85
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression.gtTransverseEuclideanIsometry_adjoint_basisFun_last
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
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirPureAxis
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTangentialCompression.gtTransverseEuclideanIsometry_adjoint_basisFun_last
    (n : ℕ) :
    (gtTransverseEuclideanIsometry n).toLinearMap.adjoint
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) = 0 := by sorry
