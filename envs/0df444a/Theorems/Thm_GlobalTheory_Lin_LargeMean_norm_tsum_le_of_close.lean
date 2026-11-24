-- Prove2me | Theorems.Thm_GlobalTheory_Lin_LargeMean_norm_tsum_le_of_close
-- name    : GlobalTheory.Lin.LargeMean.norm_tsum_le_of_close
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:06:25.811368+00:00
-- url     : https://prove2.me/theorems/ae58941d-c2f1-4245-91f1-cef46f6533bb
-- title:
--   Large Mean: norm tsum le of close
-- statement:
--   The Large Mean construction uses the norm tsum le of close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LargeMeanOfLargeDerivative.lean#L183-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LargeMeanOfLargeDerivative.lean#L183-L192

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

theorem GlobalTheory.Lin.LargeMean.norm_tsum_le_of_close {T P : ℕ → ℂ} {G : ℕ → ℝ} (hP : Summable P)
    (hG : Summable G) (h : ∀ n, ‖T n - P n‖ ≤ G n) :
    ‖∑' n, T n‖ ≤ ‖∑' n, P n‖ + ∑' n, G n := by sorry
