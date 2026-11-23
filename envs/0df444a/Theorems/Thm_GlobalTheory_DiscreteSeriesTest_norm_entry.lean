-- Prove2me | Theorems.Thm_GlobalTheory_DiscreteSeriesTest_norm_entry
-- name    : GlobalTheory.DiscreteSeriesTest.norm_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:39.429797+00:00
-- url     : https://prove2.me/theorems/3e3b7356-1e74-4070-b9f5-e300caf8058b
-- title:
--   Discrete Series Test: norm entry
-- statement:
--   The Discrete Series Test construction uses the norm entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/LowKAddStrictAnti.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/LowKAddStrictAnti.lean#L91-L97

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

theorem GlobalTheory.DiscreteSeriesTest.norm_entry {ε : Fin 1 → Bool} {g : Matrix (Fin 1) (Fin 1) ℂ} (hg : inUJ ε g) : ‖g 0 0‖ = 1 := by sorry
