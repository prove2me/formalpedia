-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_summable_norm_inner
-- name    : GroundTheory.Automorphic.IsTraceClass.summable_norm_inner
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:03.954849+00:00
-- url     : https://prove2.me/theorems/20af2e2a-a6d8-44bd-8e0a-edf7fbceb690
-- title:
--   Is Trace Class: summable norm inner
-- statement:
--   The Is Trace Class construction uses the summable norm inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L391-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L391-L394

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

theorem GroundTheory.Automorphic.IsTraceClass.summable_norm_inner {T : H →L[ℂ] H} (hT : IsTraceClass T) {ι : Type*}
    (b : HilbertBasis ι ℂ H) : Summable fun i => ‖⟪b i, T (b i)⟫_ℂ‖ := by sorry
