-- Prove2me | Theorems.Thm_GlobalTheory_NearZeroDeriv_power_sum_large
-- name    : GlobalTheory.NearZeroDeriv.power_sum_large
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:33:20.412137+00:00
-- url     : https://prove2.me/theorems/2d726256-bdb2-4c01-8a5f-55d89b279907
-- title:
--   Near Zero Deriv: power sum large
-- statement:
--   The Near Zero Deriv construction uses the power sum large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLargeVonMangoldtLogPowerSeriesNearZero.lean#L39-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLargeVonMangoldtLogPowerSeriesNearZero.lean#L39-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficientsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLargeVonMangoldtLogPowerSeriesNearZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.NearZeroDeriv

theorem GlobalTheory.NearZeroDeriv.power_sum_large {C : ℝ} (hC : 1 ≤ C)
    (hT : ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖)
    (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) (r B : ℝ) (K : ℕ) (hr : 0 < r)
    (hs : ∀ w ∈ Z, s - w ≠ 0)
    (hB : ∑ w ∈ Z, (m w : ℝ) / ‖s - w‖ ^ 2 ≤ B / r ^ 2) (hK : 4 * (8 * C) ^ 2 * B ≤ K)
    (ρ : ℂ) (hρ : ρ ∈ Z) (hm : 1 ≤ m ρ) (hd : ‖s - ρ‖ ≤ 2 * r) :
    ∃ j : ℕ, K + 1 ≤ j ∧ j ≤ 2 * K ∧
      3 / 4 * (1 / (4 * C * r)) ^ j ≤ ‖∑ w ∈ Z, (m w : ℂ) / (s - w) ^ j‖ := by sorry
