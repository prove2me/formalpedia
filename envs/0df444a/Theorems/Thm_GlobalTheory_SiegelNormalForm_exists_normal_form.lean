-- Prove2me | Theorems.Thm_GlobalTheory_SiegelNormalForm_exists_normal_form
-- name    : GlobalTheory.SiegelNormalForm.exists_normal_form
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:47.086005+00:00
-- url     : https://prove2.me/theorems/a0b97348-45ee-4913-be90-54afb55ab522
-- title:
--   Siegel Normal Form: exists normal form
-- statement:
--   The Siegel Normal Form construction uses the exists normal form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean#L177-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean#L177-L353

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.SiegelNormalForm
variable {g : ℕ}
open Complex Matrix Filter Topology
open scoped BigOperators Real
variable {g : ℕ}

theorem GlobalTheory.SiegelNormalForm.exists_normal_form : (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Bijective Ef → ∃ (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ) (Q : (Fin g → ℂ) → ℂ) (b : Fin g → ℂ), τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ (∀ j, b j ≠ 0) ∧ (∀ (i : Fin g) (l : Λ) z, (l : Fin g → ℂ) = φ (Pi.single i 1) → (χ l * cexp (Real.pi * (φ z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) = cexp (Q (z + Pi.single i 1) - Q z)) ∧ (∀ (j : Fin g) (l : Λ) z, (l : Fin g → ℂ) = φ (τ.mulVec (Pi.single j 1)) → (χ l * cexp (Real.pi * (φ z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) = b j * cexp (-(2 * Real.pi * I) * z j) * cexp (Q (z + τ.mulVec (Pi.single j 1)) - Q z))) := by sorry
