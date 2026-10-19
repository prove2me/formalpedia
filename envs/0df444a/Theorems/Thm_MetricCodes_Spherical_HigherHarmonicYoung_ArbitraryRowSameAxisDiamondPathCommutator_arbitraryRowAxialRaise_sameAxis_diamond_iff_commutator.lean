-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondPathCommutator_arbitraryRowAxialRaise_sameAxis_diamond_iff_commutator
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator.arbitraryRowAxialRaise_sameAxis_diamond_iff_commutator
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:58.135956+00:00
-- url     : https://prove2.me/theorems/9d116678-4ff3-443b-b59b-857051181a97
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator.arbitraryRowAxialRaise_sameAxis_diamond_iff_commutator
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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapShift

theorem MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator.arbitraryRowAxialRaise_sameAxis_diamond_iff_commutator
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) (hij : i < j)
    (hdom : lam j ≤ lam i) (k : Fin n) :
    ((arbitraryRowAxialRaise (raiseWeight lam i) j k).comp
        (arbitraryRowAxialRaise lam i k) =
      (arbitraryRowAxialRaise (raiseWeight lam j) i k).comp
        (arbitraryRowAxialRaise lam j k)) ↔
      ((arbitraryRowAxialRaise lam j k).comp
          (arbitraryRowAxialRaise lam i k) -
        (arbitraryRowAxialRaise lam i k).comp
          (arbitraryRowAxialRaise lam j k) =
          (diamondOmittedRowOperator lam j i k).comp
            (arbitraryRowAxialRaise lam i k)) := by sorry
