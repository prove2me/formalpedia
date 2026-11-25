-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_enorm_trace_le
-- name    : GroundTheory.Automorphic.enorm_trace_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:07:50.513738+00:00
-- url     : https://prove2.me/theorems/ec8e9d79-9c34-4f22-b9a4-ac43206c996c
-- title:
--   Automorphic: enorm trace le
-- statement:
--   The Automorphic construction uses the enorm trace le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L396-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L396-L408

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

theorem GroundTheory.Automorphic.enorm_trace_le (T : H →L[ℂ] H) : ‖trace T‖ₑ ≤ traceNorm T := by sorry
