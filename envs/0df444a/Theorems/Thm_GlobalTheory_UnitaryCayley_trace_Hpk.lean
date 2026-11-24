-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryCayley_trace_Hpk
-- name    : GlobalTheory.UnitaryCayley.trace_Hpk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:39:13.193329+00:00
-- url     : https://prove2.me/theorems/4ebd0fdf-de88-44a9-b276-c952c22da0b4
-- title:
--   Unitary Cayley: trace Hpk
-- statement:
--   The Unitary Cayley construction uses the trace Hpk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsIsCayleyUIff.lean#L94-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/ExistsIsCayleyUIff.lean#L94-L108

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsIsCayleyUIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset PI.UpqRep
noncomputable section
open GlobalTheory GlobalTheory.UnitaryCayley

theorem GlobalTheory.UnitaryCayley.trace_Hpk (k r : ℕ) : (Hpk k r).trace = (k : ℂ) - 1 := by sorry
