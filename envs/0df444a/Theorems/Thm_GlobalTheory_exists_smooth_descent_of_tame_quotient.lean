-- Prove2me | Theorems.Thm_GlobalTheory_exists_smooth_descent_of_tame_quotient
-- name    : GlobalTheory.exists_smooth_descent_of_tame_quotient
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:43:20.624359+00:00
-- url     : https://prove2.me/theorems/cb2ae4e7-632a-4857-807b-5471535a45a5
-- title:
--   Global Theory: exists smooth descent of tame quotient
-- statement:
--   The Global Theory construction uses the exists smooth descent of tame quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmoothDescentOfTameQuotient.lean#L22-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmoothDescentOfTameQuotient.lean#L22-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsAffineOpenLeOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientOfFiniteGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientExistsUniqueCompEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfIsPullbackOfSurjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsPullbackFlatOfTameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothDescentOfTameQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory

theorem GlobalTheory.exists_smooth_descent_of_tame_quotient :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X X' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) (s : X ⟶ Sp R) (τ : Γ →* Aut G.left), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsFinite π → IsQProjOver (G.hom ≫ s) → Smooth G.hom → (∀ g, (τ g).hom ≫ G.hom = G.hom ≫ (ρ g).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x → pullback.fst G.hom x ≫ (τ g).hom = pullback.fst G.hom x) → ∃ (G' : Over X') (φ : G.left ⟶ G'.left), IsPullback φ G.hom G'.hom π ∧ Smooth G'.hom ∧ ∀ g, (τ g).hom ≫ φ = φ := by sorry
