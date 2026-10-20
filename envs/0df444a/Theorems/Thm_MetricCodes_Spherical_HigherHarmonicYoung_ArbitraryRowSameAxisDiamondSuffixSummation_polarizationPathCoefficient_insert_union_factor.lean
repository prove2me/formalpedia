-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixSummation_polarizationPathCoefficient_insert_union_factor
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation.polarizationPathCoefficient_insert_union_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:00.396673+00:00
-- url     : https://prove2.me/theorems/92e050b9-421b-484c-a100-f56c956df2f0
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation.polarizationPathCoefficient_insert_union_factor
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
set_option maxHeartbeats 3000000
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor

theorem MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation.polarizationPathCoefficient_insert_union_factor
    {r : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (target pivot : Fin (r + 1)) (hpivot : pivot < target)
    (L U : Finset (Fin (r + 1)))
    (hL : L ⊆ precedingRows pivot)
    (hU : U ⊆ diamondSucceedingRows target pivot) :
    polarizationPathCoefficient lam target (insert pivot (L ∪ U)) =
      -upperDiamondPathCoefficient lam target pivot U *
        spectralPathCoeff lam pivot
          (shiftedRowGap lam target pivot + 1) L := by sorry
