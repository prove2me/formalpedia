-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_strip_finitely_many_prime_factors
-- name    : GlobalTheory.T.exists_strip_finitely_many_prime_factors
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:11.678107+00:00
-- url     : https://prove2.me/theorems/43125b3a-d64d-41da-86b0-f95822453a39
-- title:
--   T: exists strip finitely many prime factors
-- statement:
--   The T construction uses the exists strip finitely many prime factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsStripFinitelyManyPrimeFactorsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsStripFinitelyManyPrimeFactorsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStripFinitelyManyPrimeFactors
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStripFinitelyManyPrimeFactorsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_strip_finitely_many_prime_factors : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (x : R), x ≠ 0 → ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧ ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y := by sorry
