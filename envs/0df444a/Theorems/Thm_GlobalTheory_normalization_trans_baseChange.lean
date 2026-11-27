-- Prove2me | Theorems.Thm_GlobalTheory_normalization_trans_baseChange
-- name    : GlobalTheory.normalization_trans_baseChange
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:15.148842+00:00
-- url     : https://prove2.me/theorems/5d22cc68-4b0b-48ac-8b3d-fa8a4e0024a0
-- title:
--   Global Theory: normalization trans base Change
-- statement:
--   The Global Theory construction uses the normalization trans base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L1097-L1174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L1097-L1174

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
attribute [instance] PreservesNormalization.isIso_normalizationPullback

theorem GlobalTheory.normalization_trans_baseChange {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] :
    (∀ {T : Scheme.{u}} (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂] [QuasiCompact f₁]
      [QuasiSeparated f₁], f = f₁ ≫ f₂ → ∃ e : f₁.normalization ≅ f.normalization,
        f₁.toNormalization ≫ e.hom = f.toNormalization ∧
        e.hom ≫ f.fromNormalization = f₁.fromNormalization ≫ f₂) ∧
    (∀ (V : Y.Opens) [IsFinite (f ∣_ V)],
      IsIso (f.toNormalization ∣_ (f.fromNormalization ⁻¹ᵁ V))) ∧
    (∀ (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
      (s : Y ⟶ Spec (.of R)) (c : X ⟶ Spec (.of K)),
      f ≫ s = c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) →
        Flat (f.fromNormalization ≫ s)) ∧
    (∀ {X' : Scheme.{u}} (f' : X' ⟶ Y) [QuasiCompact f'] [QuasiSeparated f'] (a : X ⟶ X'),
      a ≫ f' = f → ∃! m : f.normalization ⟶ f'.normalization,
        f.toNormalization ≫ m = a ≫ f'.toNormalization ∧
        m ≫ f'.fromNormalization = f.fromNormalization) ∧
    (∀ (G : Type v) [Group G] [Finite G] (ρ : G →* Aut X), (∀ g, (ρ g).hom ≫ f = f) →
      (∃! τ : G →* Aut f.normalization, ∀ g,
        f.toNormalization ≫ (τ g).hom = (ρ g).hom ≫ f.toNormalization ∧
        (τ g).hom ≫ f.fromNormalization = f.fromNormalization) ∧
      ∀ (τ : G →* Aut f.normalization), (∀ g,
        f.toNormalization ≫ (τ g).hom = (ρ g).hom ≫ f.toNormalization ∧
        (τ g).hom ≫ f.fromNormalization = f.fromNormalization) →
      ∀ {X' : Scheme.{u}} (f' : X' ⟶ Y) [QuasiCompact f'] [QuasiSeparated f'] (π : X ⟶ X'),
        (∀ g, (ρ g).hom ≫ π = π) →
        (∀ W : X'.Opens, Function.Injective (π.app W) ∧
          Set.range (π.app W) = {s | IsInvariantSection ρ (π ⁻¹ᵁ W) s}) →
        ∀ q : f.normalization ⟶ f'.normalization,
          f.toNormalization ≫ q = π ≫ f'.toNormalization →
          q ≫ f'.fromNormalization = f.fromNormalization →
          (∀ g, (τ g).hom ≫ q = q) ∧ IsIntegralHom q ∧ Surjective q ∧
            (∀ x y, q x = q y ↔ ∃ g, (τ g).hom x = y) ∧
            ∀ W : f'.normalization.Opens, Function.Injective (q.app W) ∧
              Set.range (q.app W) = {s | IsInvariantSection τ (q ⁻¹ᵁ W) s}) ∧
    (∀ (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (M : Submonoid R)
      [IsLocalization M R'] {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') [QuasiCompact f']
      [QuasiSeparated f'] (a : X' ⟶ X) (b : Y' ⟶ Y) (t : Y' ⟶ Spec (.of R'))
      (s : Y ⟶ Spec (.of R)), IsPullback b t s (Spec.map (CommRingCat.ofHom (algebraMap R R'))) →
      IsPullback a f' f b → ∃ m : f'.normalization ⟶ f.normalization,
        f'.toNormalization ≫ m = a ≫ f.toNormalization ∧
        IsPullback m f'.fromNormalization f.fromNormalization b) ∧
    (∀ {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') [QuasiCompact f'] [QuasiSeparated f'] (a : X' ⟶ X)
      (b : Y' ⟶ Y) [Smooth b], IsPullback a f' f b →
      ∃ m : f'.normalization ⟶ f.normalization,
        f'.toNormalization ≫ m = a ≫ f.toNormalization ∧
        IsPullback m f'.fromNormalization f.fromNormalization b) := by sorry
