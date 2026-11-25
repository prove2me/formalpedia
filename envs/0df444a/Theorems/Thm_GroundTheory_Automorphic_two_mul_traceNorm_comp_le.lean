-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_two_mul_traceNorm_comp_le
-- name    : GroundTheory.Automorphic.two_mul_traceNorm_comp_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:36:24.145067+00:00
-- url     : https://prove2.me/theorems/0ce2cb9b-94bd-4c30-b4e5-30bbc2cd6646
-- title:
--   Automorphic: two mul trace Norm comp le
-- statement:
--   The Automorphic construction uses the two mul trace Norm comp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L323-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L323-L341

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

theorem GroundTheory.Automorphic.two_mul_traceNorm_comp_le (A B : H →L[ℂ] H) :
    2 * traceNorm (A.comp B) ≤ hsNormSq A + hsNormSq B := by sorry
