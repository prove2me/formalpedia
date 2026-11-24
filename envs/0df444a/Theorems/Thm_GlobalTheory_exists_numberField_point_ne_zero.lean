-- Prove2me | Theorems.Thm_GlobalTheory_exists_numberField_point_ne_zero
-- name    : GlobalTheory.exists_numberField_point_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:36:17.805517+00:00
-- url     : https://prove2.me/theorems/4a0e3218-f56e-4da4-bb70-b5cf2fc14953
-- title:
--   Global Theory: exists number Field point ne zero
-- statement:
--   The Global Theory construction uses the exists number Field point ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteTypeToNumberField.lean#L24-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteTypeToNumberField.lean#L24-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteTypeToNumberField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory

theorem GlobalTheory.exists_numberField_point_ne_zero :
    ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A →
      ∀ a : A, a ≠ 0 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (χ : A →+* K), χ a ≠ 0 := by sorry
