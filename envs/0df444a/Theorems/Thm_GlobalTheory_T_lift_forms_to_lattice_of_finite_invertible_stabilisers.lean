-- Prove2me | Theorems.Thm_GlobalTheory_T_lift_forms_to_lattice_of_finite_invertible_stabilisers
-- name    : GlobalTheory.T.lift_forms_to_lattice_of_finite_invertible_stabilisers
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:36:11.806451+00:00
-- url     : https://prove2.me/theorems/1c6129c2-6787-5c81-8e65-16bae8a03280
-- title:
--   T: lift forms to lattice of finite invertible stabilisers
-- statement:
--   The T construction uses the lift forms to lattice of finite invertible stabilisers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LiftFormsToLatticeOfFiniteInvertibleStabilisersStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LiftFormsToLatticeOfFiniteInvertibleStabilisersStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftFormsToLatticeOfFiniteInvertibleStabilisers
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftFormsToLatticeOfFiniteInvertibleStabilisersStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lift_forms_to_lattice_of_finite_invertible_stabilisers : ∀ (O : Type) [CommRing O] (G : Type) [Group G] (Γ K : Subgroup G) (B Q : Type) [AddCommGroup B] [Module O B] [AddCommGroup Q] [Module O Q] (ρ : Representation O K B) (π : B →ₗ[O] Q), Function.Surjective π → (∀ κ x, π x = 0 → π (ρ κ x) = 0) → (∀ g : G, Finite {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} ∧ IsUnit ((Nat.card {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} : ℕ) : O)) → ∀ f : G → Q, (∀ (γ : Γ) (g : G) (κ : K) (y : B), f g = π y → f ((γ : G) * g * κ) = π (ρ κ⁻¹ y)) → ∃ F ∈ Formalism.UG.AMFK O Γ K ρ, ∀ g, π (F g) = f g := by sorry
