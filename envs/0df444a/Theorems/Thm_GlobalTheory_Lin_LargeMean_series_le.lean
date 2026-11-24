-- Prove2me | Theorems.Thm_GlobalTheory_Lin_LargeMean_series_le
-- name    : GlobalTheory.Lin.LargeMean.series_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:06:21.80274+00:00
-- url     : https://prove2.me/theorems/f3af9f43-414c-4656-86e1-b6d86e55171a
-- title:
--   Large Mean: series le
-- statement:
--   The Large Mean construction uses the series le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LargeMeanOfLargeDerivative.lean#L194-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LargeMeanOfLargeDerivative.lean#L194-L216

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

theorem GlobalTheory.Lin.LargeMean.series_le (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (K k : ℕ)
    (h1 : K ≤ k) (h2 : k ≤ 2 * K) (hs : Summable fun n : ℕ => Λ n / (n : ℝ) ^ (1 + r / 2)) :
    r ^ k * ‖derSeries c k ((1 + r : ℝ) : ℂ)‖ ≤
      ‖∑ n ∈ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)),
        (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (r * Real.log (Real.exp (32 / δ * K / r))) : ℝ) : ℂ)‖ +
      (δ ^ k * ∑' n : ℕ, Λ n / (n : ℝ) ^ (1 + r / 2) +
        (4 * r) ^ k * ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by sorry
