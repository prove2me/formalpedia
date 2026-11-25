-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isTraceClass_comp
-- name    : GroundTheory.Automorphic.isTraceClass_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:08:15.199202+00:00
-- url     : https://prove2.me/theorems/7dc3b20c-3b2a-4691-8e13-c89d9d3055d2
-- title:
--   Automorphic: is Trace Class comp
-- statement:
--   The Automorphic construction uses the is Trace Class comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L343-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L343-L350

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

theorem GroundTheory.Automorphic.isTraceClass_comp {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    IsTraceClass (A.comp B) := by sorry
