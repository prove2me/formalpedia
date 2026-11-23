-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_comp_left
-- name    : GroundTheory.Automorphic.IsHilbertSchmidt.comp_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:51.789212+00:00
-- url     : https://prove2.me/theorems/af041eb1-84ad-46f4-81d4-514a884c4e7d
-- title:
--   Is Hilbert Schmidt: comp left
-- statement:
--   The Is Hilbert Schmidt construction uses the comp left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidt.lean#L167-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidt.lean#L167-L169

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

theorem GroundTheory.Automorphic.IsHilbertSchmidt.comp_left {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) (A : K →L[𝕜] L) :
    IsHilbertSchmidt (A.comp T) := by sorry
