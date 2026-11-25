-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_trace_comp_comm_of_isHilbertSchmidt
-- name    : GroundTheory.Automorphic.trace_comp_comm_of_isHilbertSchmidt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:36:02.500871+00:00
-- url     : https://prove2.me/theorems/7bb78f4a-946f-4d46-bb88-a3a01bac5cda
-- title:
--   Automorphic: trace comp comm of is Hilbert Schmidt
-- statement:
--   The Automorphic construction uses the trace comp comm of is Hilbert Schmidt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L369-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L369-L371

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

theorem GroundTheory.Automorphic.trace_comp_comm_of_isHilbertSchmidt {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) : trace (A.comp B) = trace (B.comp A) := by sorry
