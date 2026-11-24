-- Prove2me | Theorems.Thm_GlobalTheory_RepTrace_trace_lsmul_restrictScalars
-- name    : GlobalTheory.RepTrace.trace_lsmul_restrictScalars
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:22:10.256464+00:00
-- url     : https://prove2.me/theorems/c6edf5f7-abe9-451b-bd88-66e8caa5eb5a
-- title:
--   Rep Trace: trace lsmul restrict Scalars
-- statement:
--   The Rep Trace construction uses the trace lsmul restrict Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RepTraceEqMulTrace.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RepTraceEqMulTrace.lean#L21-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepTraceEqMulTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open GlobalTheory.RepTrace

theorem GlobalTheory.RepTrace.trace_lsmul_restrictScalars {K L V : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V] [FiniteDimensional L V] (a : L) :
    LinearMap.trace K V ((LinearMap.lsmul L V a).restrictScalars K) =
      (Module.finrank L V : K) * Algebra.trace K L a := by sorry
