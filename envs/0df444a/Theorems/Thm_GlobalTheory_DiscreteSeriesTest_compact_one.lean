-- Prove2me | Theorems.Thm_GlobalTheory_DiscreteSeriesTest_compact_one
-- name    : GlobalTheory.DiscreteSeriesTest.compact_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:50:38.728284+00:00
-- url     : https://prove2.me/theorems/3d2ec1ca-2378-4384-ba49-3320fea4990b
-- title:
--   Discrete Series Test: compact one
-- statement:
--   The Discrete Series Test construction uses the compact one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/LowKAddStrictAnti.lean#L126-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/LowKAddStrictAnti.lean#L126-L138

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

theorem GlobalTheory.DiscreteSeriesTest.compact_one (ε : Fin 1 → Bool) : CompactSpace (UJ ε) := by sorry
