-- Prove2me | Theorems.Thm_GlobalTheory_exists_quasiReflection_mulVec_eq
-- name    : GlobalTheory.exists_quasiReflection_mulVec_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:33:20.39094+00:00
-- url     : https://prove2.me/theorems/4164375d-e980-5acf-b012-ec6a82b3103e
-- title:
--   Global Theory: exists quasi Reflection mul Vec eq
-- statement:
--   The Global Theory construction uses the exists quasi Reflection mul Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryMulVecEqOfFormEq.lean#L44-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryMulVecEqOfFormEq.lean#L44-L73

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

theorem GlobalTheory.exists_quasiReflection_mulVec_eq {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (x y : Fin n → E)
    (hxy : star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y))
    (h0 : star (x - y) ⬝ᵥ (J *ᵥ x) ≠ 0) :
    ∃ γ : Matrix (Fin n) (Fin n) E, γᴴ * J * γ = J ∧ γ *ᵥ x = y := by sorry
