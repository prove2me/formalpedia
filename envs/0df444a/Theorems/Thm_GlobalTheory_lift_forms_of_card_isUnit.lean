-- Prove2me | Theorems.Thm_GlobalTheory_lift_forms_of_card_isUnit
-- name    : GlobalTheory.lift_forms_of_card_isUnit
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:56:29.435074+00:00
-- url     : https://prove2.me/theorems/5a3baf47-2cb9-4e16-aaef-02fc8bf1d5cf
-- title:
--   Global Theory: lift forms of card is Unit
-- statement:
--   The Global Theory construction uses the lift forms of card is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LiftFormsToLatticeOfFiniteInvertibleStabilisers.lean#L6-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LiftFormsToLatticeOfFiniteInvertibleStabilisers.lean#L6-L114

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftFormsToLatticeOfFiniteInvertibleStabilisers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.lift_forms_of_card_isUnit : ∀ (O : Type) [CommRing O] (G : Type) [Group G] (Γ K : Subgroup G)
    (B Q : Type) [AddCommGroup B] [Module O B] [AddCommGroup Q] [Module O Q]
    (ρ : Representation O K B) (π : B →ₗ[O] Q), Function.Surjective π →
    (∀ κ x, π x = 0 → π (ρ κ x) = 0) →
    (∀ g : G, Finite {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} ∧
      IsUnit ((Nat.card {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} : ℕ) : O)) →
    ∀ f : G → Q, (∀ (γ : Γ) (g : G) (κ : K) (y : B), f g = π y → f ((γ : G) * g * κ) = π (ρ κ⁻¹ y)) →
    ∃ F ∈ Formalism.UG.AMFK O Γ K ρ, ∀ g, π (F g) = f g := by sorry
