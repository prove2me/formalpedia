-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_enorm_sq_eq_tsum
-- name    : GroundTheory.Automorphic.enorm_sq_eq_tsum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:37.164223+00:00
-- url     : https://prove2.me/theorems/4ce5f4c0-8271-4908-9e5e-3a1b751807ee
-- title:
--   Automorphic: enorm sq eq tsum
-- statement:
--   The Automorphic construction uses the enorm sq eq tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidt.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidt.lean#L53-L64

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

theorem GroundTheory.Automorphic.enorm_sq_eq_tsum {ι : Type*} (b : HilbertBasis ι 𝕜 H) (x : H) :
    ‖x‖ₑ ^ 2 = ∑' i, ‖⟪b i, x⟫_𝕜‖ₑ ^ 2 := by sorry
