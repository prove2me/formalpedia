-- Prove2me | Theorems.Thm_GlobalTheory_star_form_eq_of_hermitian
-- name    : GlobalTheory.star_form_eq_of_hermitian
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:27.670058+00:00
-- url     : https://prove2.me/theorems/4ec11c2e-3e14-4c87-bcd7-86169671378c
-- title:
--   Global Theory: star form eq of hermitian
-- statement:
--   The Global Theory construction uses the star form eq of hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryMulVecEqOfFormEq.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryMulVecEqOfFormEq.lean#L17-L20

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

theorem GlobalTheory.star_form_eq_of_hermitian {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (z w : Fin n → E) :
    star (star z ⬝ᵥ (J *ᵥ w)) = star w ⬝ᵥ (J *ᵥ z) := by sorry
