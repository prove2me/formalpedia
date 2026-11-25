-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_trace_add
-- name    : GroundTheory.Automorphic.trace_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:11:16.49481+00:00
-- url     : https://prove2.me/theorems/be0a229e-75ec-4ed9-b2b3-ddf42846b86c
-- title:
--   Automorphic: trace add
-- statement:
--   The Automorphic construction uses the trace add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L410-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L410-L416

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem GroundTheory.Automorphic.trace_add {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    trace (S + T) = trace S + trace T := by sorry
