-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRankInterlacingAdjacentPathExchange_reverseInterlacingPolynomialSeed_adjacent_raise_of_rowDiamond
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange.reverseInterlacingPolynomialSeed_adjacent_raise_of_rowDiamond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:58.135956+00:00
-- url     : https://prove2.me/theorems/d5d66ae8-13aa-4791-b73c-3837903392b1
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange.reverseInterlacingPolynomialSeed_adjacent_raise_of_rowDiamond
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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamond
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungArbitraryRankAdjacentInterlacingSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingGapSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingLegalSchedule
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange.reverseInterlacingPolynomialSeed_adjacent_raise_of_rowDiamond
    {r n : ℕ}
    {low : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (hlow : Interlaces low mu) (row : Fin (r + 2))
    (hdiamond : DominantSameAxisRowDiamond (n + 1) row)
    (p : HarmonicYoungSpace (n := n) mu) :
    arbitraryRowAxialRaise low row (Fin.last n)
        (reverseInterlacingPolynomialSeed low mu p) =
      reverseInterlacingPolynomialSeed (raiseWeight low row) mu p := by sorry
