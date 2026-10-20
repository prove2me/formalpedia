-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixRootCommute_polarization_arbitraryRowAxialRaise_commutator_eq_zero_of_gt
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute.polarization_arbitraryRowAxialRaise_commutator_eq_zero_of_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:58.135956+00:00
-- url     : https://prove2.me/theorems/c580adf1-8373-4d9f-8e95-a9e0933eb6eb
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute.polarization_arbitraryRowAxialRaise_commutator_eq_zero_of_gt
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
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator

theorem MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute.polarization_arbitraryRowAxialRaise_commutator_eq_zero_of_gt
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row a b : Fin (r + 1))
    (ha : row < a) (hb : row < b) (k : Fin n)
    (p : PolynomialSpace r n) :
    polarization r n a b (arbitraryRowAxialRaise lam row k p) -
      arbitraryRowAxialRaise lam row k (polarization r n a b p) = 0 := by sorry
