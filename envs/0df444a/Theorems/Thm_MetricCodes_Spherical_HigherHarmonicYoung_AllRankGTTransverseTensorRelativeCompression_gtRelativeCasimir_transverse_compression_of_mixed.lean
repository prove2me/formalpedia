-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseTensorRelativeCompression_gtRelativeCasimir_transverse_compression_of_mixed
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression.gtRelativeCasimir_transverse_compression_of_mixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:10.573365+00:00
-- url     : https://prove2.me/theorems/5f1649b3-92a3-4250-83cf-12531be589ef
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression.gtRelativeCasimir_transverse_compression_of_mixed
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

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseTensorRelativeCompression.gtRelativeCasimir_transverse_compression_of_mixed
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (nu : Fin (r + 1) → ℕ)
    (I : (SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) nu) →ₗ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam))
    (hisom : I.adjoint.comp I = LinearMap.id)
    (hmixed : I.adjoint.comp
        ((gtMixedRotationOperator (n := n + 1) lam).comp I) =
      gtMixedRotationOperator (n := n) nu) :
    I.adjoint.comp ((gtRelativeCasimir (n := n + 1) lam).comp I) =
      gtStabilizerShiftedRelativeCasimir nu := by sorry
