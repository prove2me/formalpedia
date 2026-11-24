-- Prove2me | Theorems.Thm_GlobalTheory_Lin_LargeMean_term_eq
-- name    : GlobalTheory.Lin.LargeMean.term_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:06:37.309538+00:00
-- url     : https://prove2.me/theorems/5315ccf6-9cee-47e3-9895-fb3376eb7a56
-- title:
--   Large Mean: term eq
-- statement:
--   The Large Mean construction uses the term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LargeMeanOfLargeDerivative.lean#L91-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LargeMeanOfLargeDerivative.lean#L91-L106

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

theorem GlobalTheory.Lin.LargeMean.term_eq (c : ℕ → ℂ) (k n : ℕ) (r : ℝ) :
    (r : ℂ) ^ k * (((Λ n : ℝ) : ℂ) * c n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) *
      (n : ℂ) ^ (-((1 + r : ℝ) : ℂ))) = ((Λ n / n * pw k (r * Real.log n) : ℝ) : ℂ) * c n := by sorry
