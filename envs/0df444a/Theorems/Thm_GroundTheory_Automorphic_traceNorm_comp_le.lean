-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_traceNorm_comp_le
-- name    : GroundTheory.Automorphic.traceNorm_comp_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:11:25.461199+00:00
-- url     : https://prove2.me/theorems/8c50e6d3-e23e-49f6-a1a5-408451c11f6c
-- title:
--   Automorphic: trace Norm comp le
-- statement:
--   The Automorphic construction uses the trace Norm comp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceNormComp.lean#L25-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceNormComp.lean#L25-L57

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Definitions.Def_GroundTheory_AutomorphicForms_TraceNormComp
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

theorem GroundTheory.Automorphic.traceNorm_comp_le {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) : (traceNorm (A.comp B)).toReal ≤ hsNorm A * hsNorm B := by sorry
