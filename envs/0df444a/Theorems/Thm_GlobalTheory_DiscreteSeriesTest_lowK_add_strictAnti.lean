-- Prove2me | Theorems.Thm_GlobalTheory_DiscreteSeriesTest_lowK_add_strictAnti
-- name    : GlobalTheory.DiscreteSeriesTest.lowK_add_strictAnti
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:55.022842+00:00
-- url     : https://prove2.me/theorems/9b3abc75-454c-5348-9891-46e95b0653c9
-- title:
--   Discrete Series Test: low K add strict Anti
-- statement:
--   The Discrete Series Test construction uses the low K add strict Anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/LowKAddStrictAnti.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/LowKAddStrictAnti.lean#L36-L42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_LowKAddStrictAnti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI.UpqRep MeasureTheory Matrix Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.DiscreteSeriesTest

theorem GlobalTheory.DiscreteSeriesTest.lowK_add_strictAnti {n : ℕ} (ε : Fin n → Bool) {lam : Fin n → ℝ} (h : StrictAnti lam) :
    StrictAnti (lowK ε lam + (2 : ℝ) • rhoC ε) := by sorry
