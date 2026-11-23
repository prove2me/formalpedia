-- Prove2me | Theorems.Thm_GlobalTheory_one_mem_of_mul_mem_of_forall_prime_not_dvd
-- name    : GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:28.382794+00:00
-- url     : https://prove2.me/theorems/c4084ef0-201e-4a02-a7c8-5847138ff533
-- title:
--   Global Theory: one mem of mul mem of forall prime not dvd
-- statement:
--   The Global Theory construction uses the one mem of mul mem of forall prime not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/OneMemOfMulMemOfForallPrimeNotDvd.lean#L5-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/OneMemOfMulMemOfForallPrimeNotDvd.lean#L5-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemOfMulMemOfForallPrimeNotDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd (X : Type) [Finite X]
    (S : AddSubgroup (X → ℤ)) (hmul : ∀ f ∈ S, ∀ g ∈ S, f * g ∈ S)
    (hp : ∀ (x : X) (p : ℕ), p.Prime → ∃ f ∈ S, ¬ (p : ℤ) ∣ f x) : (1 : X → ℤ) ∈ S := by sorry
