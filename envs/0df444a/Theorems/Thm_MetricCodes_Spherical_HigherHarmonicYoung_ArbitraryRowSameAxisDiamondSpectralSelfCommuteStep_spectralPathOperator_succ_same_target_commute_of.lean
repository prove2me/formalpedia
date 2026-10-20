-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralSelfCommuteStep_spectralPathOperator_succ_same_target_commute_of
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSelfCommuteStep.spectralPathOperator_succ_same_target_commute_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:00.396673+00:00
-- url     : https://prove2.me/theorems/64d89948-c9d5-4137-803e-6df7106d2f12
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSelfCommuteStep.spectralPathOperator_succ_same_target_commute_of
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
set_option maxHeartbeats 4000000
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSelfCommuteStep
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute

theorem MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSelfCommuteStep.spectralPathOperator_succ_same_target_commute_of
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (a : Fin r) (target : Fin (r + 1))
    (htarget : a.succ ≤ target)
    (k : Fin n) (u v : ℝ)
    (hcomm : ∀ (i : Fin (r + 1)), a.castSucc ≤ i → ∀ w z : ℝ,
      (spectralPathOperator lam a.castSucc i k w).comp
          (spectralPathOperator lam a.castSucc i k z) =
        (spectralPathOperator lam a.castSucc i k z).comp
          (spectralPathOperator lam a.castSucc i k w))
    (hrtt : ∀ (i j : Fin (r + 1)),
      a.castSucc ≤ i → a.castSucc ≤ j → ∀ w z : ℝ,
        (w - z) •
            ((spectralPathOperator lam a.castSucc i k w).comp
                (spectralPathOperator lam a.castSucc j k z) -
              (spectralPathOperator lam a.castSucc j k z).comp
                (spectralPathOperator lam a.castSucc i k w)) =
          (spectralPathOperator lam a.castSucc j k w).comp
              (spectralPathOperator lam a.castSucc i k z) -
            (spectralPathOperator lam a.castSucc j k z).comp
              (spectralPathOperator lam a.castSucc i k w)) :
    (spectralPathOperator lam a.succ target k u).comp
        (spectralPathOperator lam a.succ target k v) =
      (spectralPathOperator lam a.succ target k v).comp
        (spectralPathOperator lam a.succ target k u) := by sorry
