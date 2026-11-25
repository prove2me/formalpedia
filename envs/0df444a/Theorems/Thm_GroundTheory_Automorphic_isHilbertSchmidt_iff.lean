-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isHilbertSchmidt_iff
-- name    : GroundTheory.Automorphic.isHilbertSchmidt_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:55.889864+00:00
-- url     : https://prove2.me/theorems/9d293981-7f3d-5e5a-9c5f-02d29239d6e8
-- title:
--   Automorphic: is Hilbert Schmidt iff
-- statement:
--   The Automorphic construction uses the is Hilbert Schmidt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidt.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidt.lean#L96-L98

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

theorem GroundTheory.Automorphic.isHilbertSchmidt_iff {ι : Type*} (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) :
    IsHilbertSchmidt T ↔ ∑' i, ‖T (b i)‖ₑ ^ 2 < ∞ := by sorry
