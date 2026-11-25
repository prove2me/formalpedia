-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_traceNorm_comp_right_le
-- name    : GroundTheory.Automorphic.traceNorm_comp_right_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:11:34.246531+00:00
-- url     : https://prove2.me/theorems/b93ed9c7-86ec-4f79-9be1-7ba585a21fcc
-- title:
--   Automorphic: trace Norm comp right le
-- statement:
--   The Automorphic construction uses the trace Norm comp right le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L254-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L254-L264

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

theorem GroundTheory.Automorphic.traceNorm_comp_right_le (T C : H →L[ℂ] H) :
    traceNorm (T.comp C) ≤ ‖C‖ₑ * traceNorm T := by sorry
