-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_eq_zero_of_trace_mul_eq_zero
-- name    : GlobalTheory.RegSS.eq_zero_of_trace_mul_eq_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:00:16.650309+00:00
-- url     : https://prove2.me/theorems/95e16208-4f3b-4ab5-8d9e-70f8b6535538
-- title:
--   Reg SS: eq zero of trace mul eq zero
-- statement:
--   The Reg SS construction uses the eq zero of trace mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ReducedFreeAlgebraTraceFormPerfect.lean#L8-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ReducedFreeAlgebraTraceFormPerfect.lean#L8-L27

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

theorem GlobalTheory.RegSS.eq_zero_of_trace_mul_eq_zero {F L : Type} [Field F] [CharZero F] [CommRing L]
    [Algebra F L] [Module.Finite F L] [IsReduced L] (x : L)
    (hx : ∀ y : L, Algebra.trace F L (x * y) = 0) : x = 0 := by sorry
