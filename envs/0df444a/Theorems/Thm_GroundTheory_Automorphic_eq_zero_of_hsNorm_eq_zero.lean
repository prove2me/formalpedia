-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_eq_zero_of_hsNorm_eq_zero
-- name    : GroundTheory.Automorphic.eq_zero_of_hsNorm_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:07:34.133935+00:00
-- url     : https://prove2.me/theorems/ce57405e-23f2-4e1c-bee7-840b2da7d8a8
-- title:
--   Automorphic: eq zero of hs Norm eq zero
-- statement:
--   The Automorphic construction uses the eq zero of hs Norm eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceNormComp.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceNormComp.lean#L19-L23

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

theorem GroundTheory.Automorphic.eq_zero_of_hsNorm_eq_zero {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (h : hsNorm T = 0) :
    T = 0 := by sorry
