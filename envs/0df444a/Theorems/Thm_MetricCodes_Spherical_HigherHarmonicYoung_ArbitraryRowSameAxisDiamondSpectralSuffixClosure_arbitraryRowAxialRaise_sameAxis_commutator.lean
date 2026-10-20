-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralSuffixClosure_arbitraryRowAxialRaise_sameAxis_commutator
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSuffixClosure.arbitraryRowAxialRaise_sameAxis_commutator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:00.396673+00:00
-- url     : https://prove2.me/theorems/37436c6e-972f-445b-ab7b-1e774e375684
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSuffixClosure.arbitraryRowAxialRaise_sameAxis_commutator
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
set_option maxHeartbeats 5000000
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSuffixClosure
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTT
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondUniversalPluckerCancellation

theorem MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSuffixClosure.arbitraryRowAxialRaise_sameAxis_commutator
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (pivot target : Fin (r + 1)) (hpivot : pivot < target)
    (k : Fin n) :
    (arbitraryRowAxialRaise lam target k).comp
          (arbitraryRowAxialRaise lam pivot k) -
        (arbitraryRowAxialRaise lam pivot k).comp
          (arbitraryRowAxialRaise lam target k) =
      (diamondOmittedRowOperator lam target pivot k).comp
        (arbitraryRowAxialRaise lam pivot k) := by sorry
