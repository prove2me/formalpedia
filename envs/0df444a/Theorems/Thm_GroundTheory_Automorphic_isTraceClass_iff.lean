-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isTraceClass_iff
-- name    : GroundTheory.Automorphic.isTraceClass_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:40.6121+00:00
-- url     : https://prove2.me/theorems/97f11643-0331-4523-9236-6605855e6e1a
-- title:
--   Automorphic: is Trace Class iff
-- statement:
--   The Automorphic construction uses the is Trace Class iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L292-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L292-L292

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

theorem GroundTheory.Automorphic.isTraceClass_iff (T : H →L[ℂ] H) : IsTraceClass T ↔ traceNorm T < ∞ := by sorry
