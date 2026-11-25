-- Prove2me | Theorems.Thm_GlobalTheory_exists_rel_of_forall_dvd_of_card_mul
-- name    : GlobalTheory.exists_rel_of_forall_dvd_of_card_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:12.036811+00:00
-- url     : https://prove2.me/theorems/cdab2659-65ca-525c-9d05-419e4990a896
-- title:
--   Global Theory: exists rel of forall dvd of card mul
-- statement:
--   The Global Theory construction uses the exists rel of forall dvd of card mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsEqNsmulOfForallDvdOfBijective.lean#L198-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsEqNsmulOfForallDvdOfBijective.lean#L198-L276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEqNsmulOfForallDvdOfBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_rel_of_forall_dvd_of_card_mul :
    ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La), Function.Bijective EF → ∀ (N : ℕ), 0 < N → ∀ (P : Type) (T : Set P) (R : La → P → Prop), (∀ a b p, R a p → R (a + N • b) p) → (∀ a p p', R a p → R a p' → p = p') → (∀ p, ∃ a, R a p) → Nat.card P * Nat.card T = N ^ Module.finrank ℤ La → (∀ a p a' p', R a p → p ∈ T → R a' p' → (N : ℤ) ∣ EF a a') → ∀ a, (∀ a' p', R a' p' → (N : ℤ) ∣ EF a a') → ∃ p, R a p := by sorry
