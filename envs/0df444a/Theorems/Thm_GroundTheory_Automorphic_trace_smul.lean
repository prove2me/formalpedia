-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_trace_smul
-- name    : GroundTheory.Automorphic.trace_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:39.072516+00:00
-- url     : https://prove2.me/theorems/edbdf4b4-84a0-5bf4-b205-b8a39155e2a2
-- title:
--   Automorphic: trace smul
-- statement:
--   The Automorphic construction uses the trace smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L418-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L418-L425

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

theorem GroundTheory.Automorphic.trace_smul (c : ℂ) {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    trace (c • T) = c * trace T := by sorry
