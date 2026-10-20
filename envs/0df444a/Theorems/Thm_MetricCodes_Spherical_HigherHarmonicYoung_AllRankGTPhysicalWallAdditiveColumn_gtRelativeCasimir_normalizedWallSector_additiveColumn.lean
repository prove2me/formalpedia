-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalWallAdditiveColumn_gtRelativeCasimir_normalizedWallSector_additiveColumn
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalWallAdditiveColumn.gtRelativeCasimir_normalizedWallSector_additiveColumn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:14.457341+00:00
-- url     : https://prove2.me/theorems/de206c66-5370-4322-b5e5-7ce3af6c7f0f
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalWallAdditiveColumn.gtRelativeCasimir_normalizedWallSector_additiveColumn
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
set_option maxHeartbeats 4500000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalWallAdditiveColumn
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTNormalizedWallCharacteristicAnnihilation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalRetainedAdditiveColumn
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCrossBlock
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedMuAxisProjectionVanishing
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransversePhysicalDiagonalColumn
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTValidTransverseArrowheadRow
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallFullTransverseFactorization
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCrossOrthogonality
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalWallAdditiveColumn.gtRelativeCasimir_normalizedWallSector_additiveColumn
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    let hw : 2 * (r + 1) + 5 ≤ n + 1 := by omega
    let B := normalizedGTTransverseWallSector lam mu h hw hlast
    (gtRelativeCasimir (n := n + 1) lam).comp B.toLinearMap =
      (-(wallShift (n + 1) (r + 1))) • B.toLinearMap +
        (canonicalGelfandTsetlinAxisTensor lam mu h hgram).comp
          (gtTransverseAxisCrossBlock lam mu h hgram B.toLinearMap) := by sorry
