-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_linearIndependent_bounded_by_pow_of_transcendental
-- name    : GlobalTheory.T.exists_linearIndependent_bounded_by_pow_of_transcendental
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:33.318803+00:00
-- url     : https://prove2.me/theorems/3c5d46e8-4e17-4a34-b1a4-9cd6b821c9b1
-- title:
--   T: exists linear Independent bounded by pow of transcendental
-- statement:
--   The T construction uses the exists linear Independent bounded by pow of transcendental property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsManyBoundedByPowStatement.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsManyBoundedByPowStatement.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsManyBoundedByPow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsManyBoundedByPowStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_linearIndependent_bounded_by_pow_of_transcendental : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ t : F, Transcendental k t → ∃ c : ℕ, ∀ N : ℕ, ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ ((N : ℤ) - c) * Module.finrank k⟮t⟯ F ≤ n ∧ ∀ (i : Fin n) (v : Place k F), v.1 (f i) ≤ max 1 (v.1 t) ^ N := by sorry
