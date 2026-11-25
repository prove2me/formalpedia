-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_hasSum_trace
-- name    : GroundTheory.Automorphic.IsTraceClass.hasSum_trace
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:36:19.125801+00:00
-- url     : https://prove2.me/theorems/7bd18c27-d374-439a-bcbe-103dd8b9ed7c
-- title:
--   Is Trace Class: has Sum trace
-- statement:
--   The Is Trace Class construction uses the has Sum trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L373-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L373-L378

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

theorem GroundTheory.Automorphic.IsTraceClass.hasSum_trace {T : H →L[ℂ] H} (hT : IsTraceClass T) {ι : Type*}
    (b : HilbertBasis ι ℂ H) : HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) (trace T) := by sorry
