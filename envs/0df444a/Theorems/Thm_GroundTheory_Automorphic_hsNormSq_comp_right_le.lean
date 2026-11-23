-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hsNormSq_comp_right_le
-- name    : GroundTheory.Automorphic.hsNormSq_comp_right_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:23.036282+00:00
-- url     : https://prove2.me/theorems/1736b3ee-f69a-4dad-a115-736a5d9479cd
-- title:
--   Automorphic: hs Norm Sq comp right le
-- statement:
--   The Automorphic construction uses the hs Norm Sq comp right le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidt.lean#L160-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidt.lean#L160-L165

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
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
variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
  {L : Type*} [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]

theorem GroundTheory.Automorphic.hsNormSq_comp_right_le (T : K →L[𝕜] L) (B : H →L[𝕜] K) :
    hsNormSq (T.comp B) ≤ ‖B‖ₑ ^ 2 * hsNormSq T := by sorry
