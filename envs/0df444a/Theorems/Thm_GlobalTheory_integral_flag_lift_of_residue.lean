-- Prove2me | Theorems.Thm_GlobalTheory_integral_flag_lift_of_residue
-- name    : GlobalTheory.integral_flag_lift_of_residue
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:47:12.977439+00:00
-- url     : https://prove2.me/theorems/a0631a7f-3997-5679-8aee-a1cff9256295
-- title:
--   Global Theory: integral flag lift of residue
-- statement:
--   The Global Theory construction uses the integral flag lift of residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralFlagLiftOfResidue.lean#L6-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralFlagLiftOfResidue.lean#L6-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralFlagLiftOfResidue
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

theorem GlobalTheory.integral_flag_lift_of_residue : ∀ (O Γ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Group Γ] (n a t : ℕ) (r : Γ →* GL (Fin n) O) (ρ : Γ →* GL (Fin a) O) (ψ : Fin t → Γ →* Oˣ) (ϖ : O), Irreducible ϖ → a + t = n → (∀ g m, ((r g : Matrix (Fin n) (Fin n) O).charpoly - (ρ g : Matrix (Fin a) (Fin a) O).charpoly * ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : Oˣ) : O))).coeff m ∈ IsLocalRing.maximalIdeal O) → (∀ (k Γ : Type) [Field k] [Group Γ] (n a t : ℕ) (r : Γ →* GL (Fin n) k) (ρ : Γ →* GL (Fin a) k) (ψ : Fin t → Γ →* kˣ), a + t = n → (∀ g, (r g : Matrix (Fin n) (Fin n) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly * ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : kˣ) : k))) → ∃ (R : ℕ) (V : Fin (R + 1) → Submodule k (Fin n → k)) (rs : Fin t → Fin R), V 0 = ⊥ ∧ V (Fin.last R) = ⊤ ∧ Monotone V ∧ (∀ g j x, x ∈ V j → (r g : Matrix (Fin n) (Fin n) k).mulVec x ∈ V j) ∧ Function.Injective rs ∧ ∀ s, ∃ x ∈ V (rs s).succ, x ∉ V (rs s).castSucc ∧ V (rs s).succ = V (rs s).castSucc ⊔ Submodule.span k {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) k).mulVec x - ((ψ s g : kˣ) : k) • x ∈ V (rs s).castSucc) → ∃ (R : ℕ) (M : Fin (R + 1) → Submodule O (Fin n → O)) (rs : Fin t → Fin R), (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → O, x = fun i => ϖ * y i) ∧ M (Fin.last R) = ⊤ ∧ Monotone M ∧ (∀ g j x, x ∈ M j → (r g : Matrix (Fin n) (Fin n) O).mulVec x ∈ M j) ∧ Function.Injective rs ∧ ∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧ M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span O {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) O).mulVec x - (fun i => ((ψ s g : Oˣ) : O) * x i) ∈ M (rs s).castSucc := by sorry
