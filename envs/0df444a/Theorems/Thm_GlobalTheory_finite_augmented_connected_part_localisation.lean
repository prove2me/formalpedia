-- Prove2me | Theorems.Thm_GlobalTheory_finite_augmented_connected_part_localisation
-- name    : GlobalTheory.finite_augmented_connected_part_localisation
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:54.406507+00:00
-- url     : https://prove2.me/theorems/6cfdfbc0-1502-5c2b-b528-a19a471209e6
-- title:
--   Global Theory: finite augmented connected part localisation
-- statement:
--   The Global Theory construction uses the finite augmented connected part localisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/FiniteAugmentedConnectedPartLocalisation.lean#L8-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/FiniteAugmentedConnectedPartLocalisation.lean#L8-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MonicEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_FiniteAugmentedConnectedPartLocalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.finite_augmented_connected_part_localisation :
    ∀ (F : Type) [Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : W), (∀ a : W, ¬ IsUnit a → ∃ n : ℕ, a ^ n ∈ Ideal.span {p}) → ∀ (A : Type) [CommRing A] [Algebra W A] [Module.Finite W A] (aug : A →ₐ[W] W), ∃ s : A, Function.Surjective (algebraMap A (Localization.Away s)) ∧ (∃ m : ℕ, ((RingHom.ker aug).map (algebraMap A (Localization.Away s))) ^ m ≤ Ideal.span {algebraMap W (Localization.Away s) p}) ∧ ∀ (R : Type) [CommRing R] [Algebra W R] (w : A →ₐ[W] R), (∀ t ∈ RingHom.ker aug, IsNilpotent (w t)) → IsUnit (w s) := by sorry
