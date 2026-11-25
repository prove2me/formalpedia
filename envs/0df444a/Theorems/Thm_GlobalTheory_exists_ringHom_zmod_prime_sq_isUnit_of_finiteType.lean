-- Prove2me | Theorems.Thm_GlobalTheory_exists_ringHom_zmod_prime_sq_isUnit_of_finiteType
-- name    : GlobalTheory.exists_ringHom_zmod_prime_sq_isUnit_of_finiteType
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:52.995584+00:00
-- url     : https://prove2.me/theorems/b8340a86-4ec6-5f03-8d22-4dad987c2e6e
-- title:
--   Global Theory: exists ring Hom zmod prime sq is Unit of finite Type
-- statement:
--   The Global Theory construction uses the exists ring Hom zmod prime sq is Unit of finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/FiniteTypeToModPSquared.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/FiniteTypeToModPSquared.lean#L8-L35

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_NumberFieldToModPSquared
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FiniteTypeToNumberField
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FiniteTypeToModPSquared
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

theorem GlobalTheory.exists_ringHom_zmod_prime_sq_isUnit_of_finiteType :
    ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A → ∀ a : A, a ≠ 0 → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ χ : A →+* ZMod (p ^ 2), IsUnit (χ a) := by sorry
