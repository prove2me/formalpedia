-- Prove2me | Theorems.Thm_GlobalTheory_exists_lift_of_smooth_of_isAffineOpen
-- name    : GlobalTheory.exists_lift_of_smooth_of_isAffineOpen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:50.611833+00:00
-- url     : https://prove2.me/theorems/e60046cc-9060-486c-a087-8a43d11033a8
-- title:
--   Global Theory: exists lift of smooth of is Affine Open
-- statement:
--   The Global Theory construction uses the exists lift of smooth of is Affine Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L38-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L38-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S)

theorem GlobalTheory.exists_lift_of_smooth_of_isAffineOpen [Smooth f] {U : S.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) {B C : CommRingCat.{u}}
    (π : B ⟶ C) (s : Spec B ⟶ S) (x₀ : Spec C ⟶ X) (h : x₀ ≫ f = Spec.map π ≫ s)
    (hs : Set.range s ⊆ U) (hx : Set.range x₀ ⊆ V)
    (H : ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A]
      [Algebra R B] [Algebra R C] (π' : B →ₐ[R] C), (∀ b, π' b = π b) →
      ∀ φ : A →ₐ[R] C, ∃ ψ : A →ₐ[R] B, π'.comp ψ = φ) :
    ∃ x : Spec B ⟶ X, Spec.map π ≫ x = x₀ ∧ x ≫ f = s := by sorry
