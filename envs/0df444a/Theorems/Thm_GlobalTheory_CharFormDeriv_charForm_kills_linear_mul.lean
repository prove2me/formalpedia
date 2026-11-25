-- Prove2me | Theorems.Thm_GlobalTheory_CharFormDeriv_charForm_kills_linear_mul
-- name    : GlobalTheory.CharFormDeriv.charForm_kills_linear_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:58:22.428195+00:00
-- url     : https://prove2.me/theorems/34f13e5d-f4fe-4949-bc7f-8d5adc64678d
-- title:
--   Char Form Deriv: char Form kills linear mul
-- statement:
--   The Char Form Deriv construction uses the char Form kills linear mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L241-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L241-L286

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharFormDeriv

theorem GlobalTheory.CharFormDeriv.charForm_kills_linear_mul : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (T : SchwartzMap V ℂ →L[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (f g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * f x) → T g = 0 := by sorry
