-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_tracePerfect
-- name    : GlobalTheory.RegSS.tracePerfect
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:25:22.441626+00:00
-- url     : https://prove2.me/theorems/e37f7379-05f4-5e45-bc9e-d933d48a135e
-- title:
--   Reg SS: trace Perfect
-- statement:
--   The Reg SS construction uses the trace Perfect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ReducedFreeAlgebraTraceFormPerfect.lean#L33-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ReducedFreeAlgebraTraceFormPerfect.lean#L33-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ReducedFreeAlgebraTraceFormPerfect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RegSS
open GlobalTheory GlobalTheory.RegSS

theorem GlobalTheory.RegSS.tracePerfect : TracePerfect := by sorry
