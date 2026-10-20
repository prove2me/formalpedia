-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralRTTStep_spectralPathOperator_succ_rtt_of
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTTStep.spectralPathOperator_succ_rtt_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:00.396673+00:00
-- url     : https://prove2.me/theorems/3d10c8a4-889c-49a5-ab17-b4f3f3104d20
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTTStep.spectralPathOperator_succ_rtt_of
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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTTStep
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractRTT

theorem MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTTStep.spectralPathOperator_succ_rtt_of
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (a : Fin r) (s t : Fin (r + 1))
    (hs : a.succ ≤ s) (ht : a.succ ≤ t)
    (k : Fin n) (u v : ℝ)
    (hself : ∀ w z : ℝ,
      (spectralPathOperator lam a.castSucc a.castSucc k w).comp
          (spectralPathOperator lam a.castSucc a.castSucc k z) =
        (spectralPathOperator lam a.castSucc a.castSucc k z).comp
          (spectralPathOperator lam a.castSucc a.castSucc k w))
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
    (u - v) •
        ((spectralPathOperator lam a.succ s k u).comp
            (spectralPathOperator lam a.succ t k v) -
          (spectralPathOperator lam a.succ t k v).comp
            (spectralPathOperator lam a.succ s k u)) =
      (spectralPathOperator lam a.succ t k u).comp
          (spectralPathOperator lam a.succ s k v) -
        (spectralPathOperator lam a.succ t k v).comp
          (spectralPathOperator lam a.succ s k u) := by sorry
