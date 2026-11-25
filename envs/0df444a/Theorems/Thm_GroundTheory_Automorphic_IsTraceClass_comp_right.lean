-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_comp_right
-- name    : GroundTheory.Automorphic.IsTraceClass.comp_right
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:36:53.106576+00:00
-- url     : https://prove2.me/theorems/fa9dfadf-a50c-4753-9449-9cfd29981154
-- title:
--   Is Trace Class: comp right
-- statement:
--   The Is Trace Class construction uses the comp right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L306-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L306-L308

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_comp_right

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

theorem GroundTheory.Automorphic.IsTraceClass.comp_right {T : H →L[ℂ] H} (hT : IsTraceClass T) (C : H →L[ℂ] H) :
    IsTraceClass (T.comp C) := by sorry
