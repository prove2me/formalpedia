-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallFullTransverseFactorization_gtTransverseWallTensorEmbedding_range_eq_fullTransverse
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallFullTransverseFactorization.gtTransverseWallTensorEmbedding_range_eq_fullTransverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:14.457341+00:00
-- url     : https://prove2.me/theorems/231ce238-f8b3-4201-97c7-50d959aaeb99
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallFullTransverseFactorization.gtTransverseWallTensorEmbedding_range_eq_fullTransverse
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
open scoped InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallFullTransverseFactorization
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallFullTransverseFactorization.gtTransverseWallTensorEmbedding_range_eq_fullTransverse
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    LinearMap.range
        (gtTransverseWallTensorEmbedding lam mu h hn hlast).toLinearMap =
      LinearMap.range
        (gtFullTransverseEmbedding lam hn
          (gtWallFullBranch lam mu h hlast)).toLinearMap := by sorry
