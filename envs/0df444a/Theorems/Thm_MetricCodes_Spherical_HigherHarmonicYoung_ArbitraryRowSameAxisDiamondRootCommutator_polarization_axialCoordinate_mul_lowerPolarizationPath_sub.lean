-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondRootCommutator_polarization_axialCoordinate_mul_lowerPolarizationPath_sub
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator.polarization_axialCoordinate_mul_lowerPolarizationPath_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:58.135956+00:00
-- url     : https://prove2.me/theorems/c21b9155-1e1a-4771-b4ea-7c97a8f891e2
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator.polarization_axialCoordinate_mul_lowerPolarizationPath_sub
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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator

theorem MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator.polarization_axialCoordinate_mul_lowerPolarizationPath_sub
    {r n : ℕ} (a b start : Fin (r + 1)) (k : Fin n)
    (path : List (Fin (r + 1))) (p : PolynomialSpace r n) :
    polarization r n a b
        (MvPolynomial.X (variableIndex start k) *
          lowerPolarizationPath path p) -
        MvPolynomial.X (variableIndex start k) *
          lowerPolarizationPath path (polarization r n a b p) =
      (if b = start then
        MvPolynomial.X (variableIndex a k) *
          lowerPolarizationPath path p
      else 0) +
        MvPolynomial.X (variableIndex start k) *
          upperPolarizationPathCommutator a b path p := by sorry
