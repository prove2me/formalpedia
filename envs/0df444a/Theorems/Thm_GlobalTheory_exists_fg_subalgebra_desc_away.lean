-- Prove2me | Theorems.Thm_GlobalTheory_exists_fg_subalgebra_desc_away
-- name    : GlobalTheory.exists_fg_subalgebra_desc_away
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:18.819566+00:00
-- url     : https://prove2.me/theorems/a6ea27f2-ffcb-432c-8abc-91f5dc6b7c81
-- title:
--   Global Theory: exists fg subalgebra desc away
-- statement:
--   The Global Theory construction uses the exists fg subalgebra desc away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFgSubalgebraDescAway.lean#L20-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFgSubalgebraDescAway.lean#L20-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAwaySubalgebraEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFgSubalgebraDescAway
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_fg_subalgebra_desc_away : ∀ (K : Type) [Field K] (S : Type) [CommRing S] [Algebra K S] (S₀ : Subalgebra K S), S₀.FG → ∀ (n : ℕ) (h : Fin n → S) (A : Fin n → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)], (∀ i, Algebra.FiniteType K (A i)) → ∀ a : ∀ i, A i →ₐ[K] Localization.Away (h i), Ideal.span (Set.range h) = ⊤ → ∃ (S₁ : Subalgebra K S) (h₁ : Fin n → S₁), S₁.FG ∧ S₀ ≤ S₁ ∧ (∀ i, (h₁ i : S) = h i) ∧ Ideal.span (Set.range h₁) = ⊤ ∧ ∀ i, ∃ (κ : Localization.Away (h₁ i) →ₐ[K] Localization.Away (h i)) (a' : A i →ₐ[K] Localization.Away (h₁ i)), (∀ s : S₁, κ (algebraMap S₁ _ s) = algebraMap S _ (s : S)) ∧ Function.Injective κ ∧ κ.comp a' = a i := by sorry
