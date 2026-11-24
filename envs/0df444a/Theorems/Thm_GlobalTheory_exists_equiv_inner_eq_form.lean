-- Prove2me | Theorems.Thm_GlobalTheory_exists_equiv_inner_eq_form
-- name    : GlobalTheory.exists_equiv_inner_eq_form
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:31:44.258299+00:00
-- url     : https://prove2.me/theorems/84786d19-ec0f-45b8-a5a6-cfcc3d5c4b47
-- title:
--   Global Theory: exists equiv inner eq form
-- statement:
--   The Global Theory construction uses the exists equiv inner eq form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FourierInversionHaarSymmForm.lean#L32-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FourierInversionHaarSymmForm.lean#L32-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FourierInversionHaarSymmForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory FourierTransform
open GlobalTheory
open MeasureTheory FourierTransform

theorem GlobalTheory.exists_equiv_inner_eq_form {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : V ≃L[ℝ] E) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ x y, B x y = B y x) (hn : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∃ R : V ≃L[ℝ] E, ∀ x y, B x y = inner ℝ (T x) (R y) := by sorry
