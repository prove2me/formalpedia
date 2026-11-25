-- Prove2me | Theorems.Thm_GlobalTheory_exists_dual_forms_of_separated_types
-- name    : GlobalTheory.exists_dual_forms_of_separated_types
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:54:54.569797+00:00
-- url     : https://prove2.me/theorems/28b8f534-b87e-4f99-9491-7845e49385f2
-- title:
--   Global Theory: exists dual forms of separated types
-- statement:
--   The Global Theory construction uses the exists dual forms of separated types property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsDualFormsOfSeparatedTypes.lean#L31-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsDualFormsOfSeparatedTypes.lean#L31-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsDualFormsOfSeparatedTypes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_dual_forms_of_separated_types :
    ∀ (O A : Type) [CommRing O] (d : ℕ) (ρ : A → Matrix (Fin d) (Fin d) O) (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (σ : T → A → O) (u : (Σ t : T, Fin (r t)) → Fin d → O), (∀ t t', t ≠ t' → ∃ a, IsUnit (σ t a - σ t' a)) → (∀ a l, (ρ a).mulVec (u l) = σ l.1 a • u l) → (∀ t, ∃ lam : Fin (r t) → Fin d → O, ∀ i i', ∑ s, lam i s * u ⟨t, i'⟩ s = if i = i' then 1 else 0) → ∃ lam : (Σ t : T, Fin (r t)) → Fin d → O, ∀ l l', ∑ s, lam l s * u l' s = if l = l' then 1 else 0 := by sorry
