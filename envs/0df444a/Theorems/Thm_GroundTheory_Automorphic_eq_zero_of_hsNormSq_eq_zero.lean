-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_eq_zero_of_hsNormSq_eq_zero
-- name    : GroundTheory.Automorphic.eq_zero_of_hsNormSq_eq_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:07:20.809472+00:00
-- url     : https://prove2.me/theorems/421f09e2-83bf-427f-8675-61c9f691b26d
-- title:
--   Automorphic: eq zero of hs Norm Sq eq zero
-- statement:
--   The Automorphic construction uses the eq zero of hs Norm Sq eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceNormComp.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceNormComp.lean#L13-L17

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

theorem GroundTheory.Automorphic.eq_zero_of_hsNormSq_eq_zero {T : H →L[ℂ] H} (h : hsNormSq T = 0) : T = 0 := by sorry
