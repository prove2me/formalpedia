-- Prove2me | Theorems.Thm_GlobalTheory_NearZeroDeriv_power_sum_mult
-- name    : GlobalTheory.NearZeroDeriv.power_sum_mult
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:27.933796+00:00
-- url     : https://prove2.me/theorems/d031fdc4-1e9b-4228-a59b-6934fccdab3c
-- title:
--   Near Zero Deriv: power sum mult
-- statement:
--   The Near Zero Deriv construction uses the power sum mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLargeVonMangoldtLogPowerSeriesNearZero.lean#L11-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLargeVonMangoldtLogPowerSeriesNearZero.lean#L11-L37

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

theorem GlobalTheory.NearZeroDeriv.power_sum_mult {C : ℝ} (hC : 1 ≤ C)
    (hT : ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖)
    (Z : Finset ℂ) (m : ℂ → ℕ) (f : ℂ → ℂ) (K : ℕ) (hK : ∑ w ∈ Z, m w ≤ K) (ρ : ℂ) (hρ : ρ ∈ Z)
    (hm : 1 ≤ m ρ) : ∃ j : ℕ, K + 1 ≤ j ∧ j ≤ 2 * K ∧
      (‖f ρ‖ / (2 * C)) ^ j ≤ ‖∑ w ∈ Z, (m w : ℂ) * f w ^ j‖ := by sorry
