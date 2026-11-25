-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isHilbertSchmidt_adjoint_iff
-- name    : GroundTheory.Automorphic.isHilbertSchmidt_adjoint_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:34.798438+00:00
-- url     : https://prove2.me/theorems/2dae767c-d891-448a-b767-ff0d1fb1aa2a
-- title:
--   Automorphic: is Hilbert Schmidt adjoint iff
-- statement:
--   The Automorphic construction uses the is Hilbert Schmidt adjoint iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidt.lean#L100-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidt.lean#L100-L102

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

theorem GroundTheory.Automorphic.isHilbertSchmidt_adjoint_iff (T : H →L[𝕜] K) :
    IsHilbertSchmidt (T†) ↔ IsHilbertSchmidt T := by sorry
