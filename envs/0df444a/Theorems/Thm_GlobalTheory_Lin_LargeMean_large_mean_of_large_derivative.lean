-- Prove2me | Theorems.Thm_GlobalTheory_Lin_LargeMean_large_mean_of_large_derivative
-- name    : GlobalTheory.Lin.LargeMean.large_mean_of_large_derivative
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:04:55.663216+00:00
-- url     : https://prove2.me/theorems/8f42f584-c364-42ed-b8e1-571de38f019b
-- title:
--   Large Mean: large mean of large derivative
-- statement:
--   The Large Mean construction uses the large mean of large derivative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LargeMeanOfLargeDerivative.lean#L247-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LargeMeanOfLargeDerivative.lean#L247-L343

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsTsumVonMangoldtDivRpowLeDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPrimesIocEqSumIndicator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntervalIntegrableDivOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LargeMeanOfLargeDerivative
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
noncomputable section
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.LargeMean

theorem GlobalTheory.Lin.LargeMean.large_mean_of_large_derivative : ∀ A : ℝ, 1 ≤ A → ∃ a b C r₀ K₀ : ℝ, 0 < a ∧ a < b ∧ 0 < C ∧ 0 < r₀ ∧ ∀ (c : ℕ → ℂ) (r : ℝ) (K k : ℕ), (∀ n, ‖c n‖ ≤ 1) → 0 < r → r ≤ r₀ → K₀ ≤ K → K ≤ k → k ≤ 2 * K → 1 / (A * r) ^ (k + 1) ≤ ‖derSeries c k ((1 + r : ℝ) : ℂ)‖ → Real.exp (-(C * K)) / r ^ 3 ≤ ∫ y in (Real.exp (a * K / r))..(Real.exp (b * K / r)), ‖∑ p ∈ primesIoc (Real.exp (a * K / r)) y, (Real.log p : ℂ) * c p / p‖ ^ 2 / y := by sorry
