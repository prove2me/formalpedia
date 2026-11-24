-- Prove2me | Theorems.Thm_GlobalTheory_T_one_mem_of_mul_mem_of_forall_prime_exists_not_dvd
-- name    : GlobalTheory.T.one_mem_of_mul_mem_of_forall_prime_exists_not_dvd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:53:59.204376+00:00
-- url     : https://prove2.me/theorems/b88c6432-745c-4eee-ac26-8861035dccc1
-- title:
--   T: one mem of mul mem of forall prime exists not dvd
-- statement:
--   The T construction uses the one mem of mul mem of forall prime exists not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/OneMemOfMulMemOfForallPrimeNotDvdStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/OneMemOfMulMemOfForallPrimeNotDvdStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemOfMulMemOfForallPrimeNotDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemOfMulMemOfForallPrimeNotDvdStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.one_mem_of_mul_mem_of_forall_prime_exists_not_dvd : ∀ (X : Type) [Finite X] (S : AddSubgroup (X → ℤ)), (∀ f ∈ S, ∀ g ∈ S, f * g ∈ S) → (∀ (x : X) (p : ℕ), p.Prime → ∃ f ∈ S, ¬ (p : ℤ) ∣ f x) → (1 : X → ℤ) ∈ S := by sorry
