-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedProjectorCompression_reverseInterlacing_projectedCoordinateLower_sameAxis_eq_plusProbability_of_minor
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression.reverseInterlacing_projectedCoordinateLower_sameAxis_eq_plusProbability_of_minor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:06.385168+00:00
-- url     : https://prove2.me/theorems/3bce8bfa-4d6c-4101-a958-a707868e0541
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression.reverseInterlacing_projectedCoordinateLower_sameAxis_eq_plusProbability_of_minor
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
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedProjectorCompression.reverseInterlacing_projectedCoordinateLower_sameAxis_eq_plusProbability_of_minor
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (hlow : Interlaces low mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (hfinite : FiniteInterlacing (n + 1) low mu)
    (hdom : Antitone low) (row : Fin (r + 2))
    (hminor : ∀ p q : HarmonicYoungSpace (n := n) mu,
      gtAxisCompressedCharacteristicMinor low mu hlow hgram p q =
        Polynomial.C ⟪p, q⟫_ℝ *
          channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
            (stabilizerShift (n + 1) mu))
    (hselected : ∀ p : HarmonicYoungSpace (n := n) mu,
      allRankCartanCharacteristicProjector low (row, true)
          (canonicalGelfandTsetlinAxisTensor low mu hlow hgram p) =
        gtSelectedRowClebschRangeProjector low row
          (canonicalGelfandTsetlinAxisTensor low mu hlow hgram p))
    (hrange : ∀ p : HarmonicYoungSpace (n := n) mu,
      gtSelectedPhysicalAxisCompression low row
          (canonicalGelfandTsetlinFibre low mu hlow hgram p) ∈
        LinearMap.range
          (canonicalGelfandTsetlinFibre low mu hlow hgram).toLinearMap)
    (p : HarmonicYoungSpace (n := n) mu) :
    projectedCoordinateLower low (raiseWeight low row)
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (arbitraryRowSameAxisHarmonicRaise low hdom row (Fin.last n)
          (reverseInterlacingHarmonicBranch low mu hlow p)) =
      (arbitraryRowAxialLowerScalar low row *
        internalRowLowerGramScalar (raiseWeight low row) row *
        plusProbability (n + 1) low mu row) •
        reverseInterlacingHarmonicBranch low mu hlow p := by sorry
