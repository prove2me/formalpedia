-- Prove2me | Theorems.Thm_GlobalTheory_T_modulation_invariant_functional_kills_linear_multiple
-- name    : GlobalTheory.T.modulation_invariant_functional_kills_linear_multiple
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:36:16.292996+00:00
-- url     : https://prove2.me/theorems/ed411b51-23e4-4719-b7a2-4c4e54b394dc
-- title:
--   T: modulation invariant functional kills linear multiple
-- statement:
--   The T construction uses the modulation invariant functional kills linear multiple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslationInvariantFunctionalLinearZeroStatement.lean#L5-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslationInvariantFunctionalLinearZeroStatement.lean#L5-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslationInvariantFunctionalLinearZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslationInvariantFunctionalLinearZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.modulation_invariant_functional_kills_linear_multiple : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (h g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * h x) → T g = 0 := by sorry
