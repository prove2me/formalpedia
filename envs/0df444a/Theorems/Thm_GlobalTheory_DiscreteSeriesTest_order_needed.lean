-- Prove2me | Theorems.Thm_GlobalTheory_DiscreteSeriesTest_order_needed
-- name    : GlobalTheory.DiscreteSeriesTest.order_needed
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:51.579869+00:00
-- url     : https://prove2.me/theorems/c656461a-1d4d-52c3-9474-f5f399556718
-- title:
--   Discrete Series Test: order needed
-- statement:
--   The Discrete Series Test construction uses the order needed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/LowKAddStrictAnti.lean#L195-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/LowKAddStrictAnti.lean#L195-L215

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

theorem GlobalTheory.DiscreteSeriesTest.order_needed :
    lowK ![true, false] ![1 / 2, 7 / 2] = lowK ![false, true] ![5 / 2, 3 / 2] ∘ Equiv.swap 0 1 := by sorry
