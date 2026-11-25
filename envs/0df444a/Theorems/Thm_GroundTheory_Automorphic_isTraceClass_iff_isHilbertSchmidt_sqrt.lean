-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isTraceClass_iff_isHilbertSchmidt_sqrt
-- name    : GroundTheory.Automorphic.isTraceClass_iff_isHilbertSchmidt_sqrt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:07:38.661454+00:00
-- url     : https://prove2.me/theorems/85eb030f-6dd5-40f8-a005-2b1f5fbb8e41
-- title:
--   Automorphic: is Trace Class iff is Hilbert Schmidt sqrt
-- statement:
--   The Automorphic construction uses the is Trace Class iff is Hilbert Schmidt sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L117-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L117-L119

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

theorem GroundTheory.Automorphic.isTraceClass_iff_isHilbertSchmidt_sqrt (T : H →L[ℂ] H) :
    IsTraceClass T ↔ IsHilbertSchmidt (CFC.sqrt (CFC.abs T)) := by sorry
