-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCanonicalForwardAxisRange_projectedCoordinateRaise_reverseInterlacingHarmonicBranch_mem_range_of_pathExchange
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalForwardAxisRange.projectedCoordinateRaise_reverseInterlacingHarmonicBranch_mem_range_of_pathExchange
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:56.928481+00:00
-- url     : https://prove2.me/theorems/048a994e-ec40-4c1f-a37a-ab2a3fed8024
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalForwardAxisRange.projectedCoordinateRaise_reverseInterlacingHarmonicBranch_mem_range_of_pathExchange
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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalForwardAxisRange
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawForwardAxisRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowBaseAxisChannel
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowUnconditionalBranch
open MetricCodes.Spherical.HigherYoungIteratedAxialProjectionSemigroup
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherRepresentationGraph

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalForwardAxisRange.projectedCoordinateRaise_reverseInterlacingHarmonicBranch_mem_range_of_pathExchange
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hdom : Antitone low)
    (coefficient : ℝ)
    (hexchange : ∀ p : HarmonicYoungSpace (n := n) mu,
      arbitraryRowAxialRaise low row (Fin.last n)
          (reverseInterlacingPolynomialSeed low mu p) -
        coefficient •
          reverseInterlacingPolynomialSeed (raiseWeight low row) mu p ∈
        youngGramRadialIdeal (r + 1) (n + 1))
    (p : HarmonicYoungSpace (n := n) mu) :
    projectedCoordinateRaise (raiseWeight low row) low
        (sum_raiseWeight low row) row
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
        (reverseInterlacingHarmonicBranch (n := n) low mu hlow p) ∈
      LinearMap.range
        (reverseInterlacingHarmonicBranch
          (n := n) (raiseWeight low row) mu hhigh) := by sorry
