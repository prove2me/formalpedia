-- Prove2me | Theorems.Thm_GlobalTheory_holomorphic_hom_determined
-- name    : GlobalTheory.holomorphic_hom_determined
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:49:26.460105+00:00
-- url     : https://prove2.me/theorems/39009f55-14e2-4442-995b-dffe9ae50724
-- title:
--   Global Theory: holomorphic hom determined
-- statement:
--   The Global Theory construction uses the holomorphic hom determined property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L647-L690
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HolomorphicHomDetermined.lean#L647-L690

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open HolHom

theorem GlobalTheory.holomorphic_hom_determined (S : Scheme.{0}) (G : Over S) [GrpObj G] :
    (∀ (y : Sp ℂ ⟶ S) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (e e' : V → (Over.mk y ⟶ G)),
      (∀ z w, e (z + w) = e z * e w) → (∀ z w, e' (z + w) = e' z * e' w) →
      IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => (e' z).left) →
      (∀ U : G.left.Opens, ⊤ ≤ (e 0).left ⁻¹ᵁ U → ∀ f : Γ(G.left, U),
        fderiv ℂ (fun z => valAt' (e z).left U f) 0 = fderiv ℂ (fun z => valAt' (e' z).left U f) 0) → e = e') ∧
    (∀ (y : Sp ℂ ⟶ S) (n : ℕ) (e : (Fin n → ℂ) → (Over.mk y ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) →
      (∀ z₀, ∃! v : Sp (DualNumber ℂ) ⟶ G.left, IsDerivAt0 (fun z => (e z).left) z₀ v) ∧
      (∀ z₀ v, IsDerivAt0 (fun z => (e z).left) z₀ v → v ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) ∧
      ∀ (a₁ a₂ : ℂ) (z₁ z₂ : Fin n → ℂ) (v₁ v₂ v : Sp (DualNumber ℂ) ⟶ G.left),
        IsDerivAt0 (fun z => (e z).left) z₁ v₁ → IsDerivAt0 (fun z => (e z).left) z₂ v₂ →
        IsDerivAt0 (fun z => (e z).left) (a₁ • z₁ + a₂ • z₂) v →
        ∀ U : G.left.Opens, ⊤ ≤ (e 0).left ⁻¹ᵁ U → ⊤ ≤ v₁ ⁻¹ᵁ U ∧ ⊤ ≤ v₂ ⁻¹ᵁ U ∧ ⊤ ≤ v ⁻¹ᵁ U ∧ ∀ f : Γ(G.left, U),
          TrivSqZeroExt.snd (valR v U f) =
            a₁ * TrivSqZeroExt.snd (valR v₁ U f) + a₂ * TrivSqZeroExt.snd (valR v₂ U f)) ∧
    (∀ (y : Sp ℂ ⟶ S) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (g : ℕ)
      (e : V → (Over.mk y ⟶ G)) (e' : (Fin g → ℂ) → (Over.mk y ⟶ G)),
      (∀ z w, e (z + w) = e z * e w) → (∀ z w, e' (z + w) = e' z * e' w) →
      IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => (e' z).left) →
      (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
        ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) →
      ∃! h : V →ₗ[ℂ] (Fin g → ℂ), ∀ z, e z = e' (h z)) ∧
    ∀ (P V : Type) [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] [NormedAddCommGroup V]
      [NormedSpace ℂ V] [FiniteDimensional ℂ V] (g : ℕ) (B : Set P) (y : P → (Sp ℂ ⟶ S))
      (e : ∀ b, V → (Over.mk (y b) ⟶ G)) (e' : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G))
      (h : P → V →ₗ[ℂ] (Fin g → ℂ)),
      IsHolTo (B ×ˢ Set.univ) (fun bz : P × V => (e bz.1 bz.2).left) →
      IsHolTo (B ×ˢ Set.univ) (fun bz : P × (Fin g → ℂ) => (e' bz.1 bz.2).left) →
      (∀ b ∈ B, ∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' b 0).left →
        ∃! w, IsDerivAt0 (fun z => (e' b z).left) w v.left) →
      (∀ b ∈ B, ∀ z, e b z = e' b (h b z)) →
      DifferentiableOn ℂ (fun b => LinearMap.toContinuousLinearMap (h b)) B ∧
        ContinuousOn (fun b => LinearMap.toContinuousLinearMap (h b)) B ∧ ∀ z, ContinuousOn (fun b => h b z) B := by sorry
