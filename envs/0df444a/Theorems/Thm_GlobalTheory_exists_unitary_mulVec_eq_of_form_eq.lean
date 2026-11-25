-- Prove2me | Theorems.Thm_GlobalTheory_exists_unitary_mulVec_eq_of_form_eq
-- name    : GlobalTheory.exists_unitary_mulVec_eq_of_form_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:00.956882+00:00
-- url     : https://prove2.me/theorems/963ca33e-e138-457c-9b0b-a12cc0e9ed31
-- title:
--   Global Theory: exists unitary mul Vec eq of form eq
-- statement:
--   The Global Theory construction uses the exists unitary mul Vec eq of form eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryMulVecEqOfFormEq.lean#L75-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryMulVecEqOfFormEq.lean#L75-L94

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

theorem GlobalTheory.exists_unitary_mulVec_eq_of_form_eq :
    ∀ (E : Type) [Field E] [CharZero E] [StarRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
      Jᴴ = J → J.det ≠ 0 → ∀ x y : Fin n → E,
      star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y) → star x ⬝ᵥ (J *ᵥ x) ≠ 0 →
      ∃ γ : Matrix (Fin n) (Fin n) E, γᴴ * J * γ = J ∧ γ *ᵥ x = y := by sorry
