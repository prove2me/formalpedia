-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_adjoint
-- name    : GroundTheory.Automorphic.IsTraceClass.adjoint
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:42:12.634044+00:00
-- url     : https://prove2.me/theorems/0f264f1b-9414-4821-a9bb-bc9df15b18bd
-- title:
--   Is Trace Class: adjoint
-- statement:
--   The Is Trace Class construction uses the adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L310-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L310-L311

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_adjoint

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

theorem GroundTheory.Automorphic.IsTraceClass.adjoint {T : H →L[ℂ] H} (hT : IsTraceClass T) : IsTraceClass (T†) := by sorry
