-- Prove2me | Theorems.Thm_GlobalTheory_conjTranspose_mul_mul_eq_of_form_eq
-- name    : GlobalTheory.conjTranspose_mul_mul_eq_of_form_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:33.291212+00:00
-- url     : https://prove2.me/theorems/b9ba74f0-7bda-4372-b8bd-9518c3ef3370
-- title:
--   Global Theory: conj Transpose mul mul eq of form eq
-- statement:
--   The Global Theory construction uses the conj Transpose mul mul eq of form eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryMulVecEqOfFormEq.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryMulVecEqOfFormEq.lean#L7-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryMulVecEqOfFormEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.conjTranspose_mul_mul_eq_of_form_eq {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J γ : Matrix (Fin n) (Fin n) E)
    (h : ∀ z w : Fin n → E, star (γ *ᵥ z) ⬝ᵥ (J *ᵥ (γ *ᵥ w)) = star z ⬝ᵥ (J *ᵥ w)) :
    γᴴ * J * γ = J := by sorry
