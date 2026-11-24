-- Prove2me | Theorems.Thm_GlobalTheory_CharInvForm_kills_linear_mul
-- name    : GlobalTheory.CharInvForm.kills_linear_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:07:42.774321+00:00
-- url     : https://prove2.me/theorems/53605339-7639-4303-9015-3c02d924c9df
-- title:
--   Char Inv Form: kills linear mul
-- statement:
--   The Char Inv Form construction uses the kills linear mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslationInvariantFunctionalLinearZero.lean#L29-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslationInvariantFunctionalLinearZero.lean#L29-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslationInvariantFunctionalLinearZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CharInvForm

theorem GlobalTheory.CharInvForm.kills_linear_mul : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (h g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * h x) → T g = 0 := by sorry
