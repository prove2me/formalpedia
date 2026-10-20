-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondResidualSuffixPartition_diamondPathOperator_eq_insertedPrefix_comp_suffix
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition.diamondPathOperator_eq_insertedPrefix_comp_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:58.135956+00:00
-- url     : https://prove2.me/theorems/125f695f-2dae-4a1e-b137-5c86a46e9dc7
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition.diamondPathOperator_eq_insertedPrefix_comp_suffix
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
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute

theorem MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition.diamondPathOperator_eq_insertedPrefix_comp_suffix
    {r n : ℕ} (target pivot : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (front : List (Fin (r + 1)))
    (next : Fin (r + 1)) (tail : List (Fin (r + 1)))
    (hsplit : ((insert pivot S).sort (· ≤ ·)) ++ [target] =
      front ++ pivot :: next :: tail) :
    diamondPathOperator target k (insert pivot S) =
      (insertedDiamondPrefix target pivot k S front next).comp
        (lowerPolarizationPath (next :: tail)) := by sorry
