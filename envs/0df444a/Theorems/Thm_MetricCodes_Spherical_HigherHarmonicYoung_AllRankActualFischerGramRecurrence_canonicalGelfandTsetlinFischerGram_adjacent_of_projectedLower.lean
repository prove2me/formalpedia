-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankActualFischerGramRecurrence_canonicalGelfandTsetlinFischerGram_adjacent_of_projectedLower
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualFischerGramRecurrence.canonicalGelfandTsetlinFischerGram_adjacent_of_projectedLower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:03.313092+00:00
-- url     : https://prove2.me/theorems/ea336fa4-af40-4086-80e4-b8cc5ff4068c
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualFischerGramRecurrence.canonicalGelfandTsetlinFischerGram_adjacent_of_projectedLower
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
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualFischerGramRecurrence
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalForwardAxisRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowBaseAxisChannel
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowUnconditionalBranch
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherRepresentationGraph

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualFischerGramRecurrence.canonicalGelfandTsetlinFischerGram_adjacent_of_projectedLower
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hdom : Antitone low)
    (hlowGram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (hhighGram : PositiveGelfandTsetlinFischerGram
      (n := n) (raiseWeight low row) mu hhigh)
    (hexchange : ∀ p : HarmonicYoungSpace (n := n) mu,
      arbitraryRowAxialRaise low row (Fin.last n)
          (reverseInterlacingPolynomialSeed low mu p) -
        reverseInterlacingPolynomialSeed (raiseWeight low row) mu p ∈
          youngGramRadialIdeal (r + 1) (n + 1))
    (hcartan : ∀ p : HarmonicYoungSpace (n := n) mu,
      projectedCoordinateLower low (raiseWeight low row)
          (sum_raiseWeight low row) row
          (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
          (arbitraryRowSameAxisHarmonicRaise low hdom row (Fin.last n)
            (reverseInterlacingHarmonicBranch low mu hlow p)) =
        (arbitraryRowAxialLowerScalar low row *
          internalRowLowerGramScalar (raiseWeight low row) row *
          plusProbability (n + 1) low mu row) •
          reverseInterlacingHarmonicBranch low mu hlow p)
    (p : HarmonicYoungSpace (n := n) mu) (hp : p ≠ 0) :
    canonicalGelfandTsetlinFischerGram
        (raiseWeight low row) mu hhigh hhighGram =
      arbitraryRowAxialLowerScalar low row ^ 2 *
        internalRowLowerGramScalar (raiseWeight low row) row *
        canonicalGelfandTsetlinFischerGram low mu hlow hlowGram *
        plusProbability (n + 1) low mu row := by sorry
