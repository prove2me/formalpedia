-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_val_lift
-- name    : GlobalTheory.CompanionTheory.Ultra.val_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:22:07.466857+00:00
-- url     : https://prove2.me/theorems/eca386e9-10e8-4b3d-b7ce-399b88514358
-- title:
--   Ultra: val lift
-- statement:
--   The Ultra construction uses the val lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L49-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsProperSpreadsOut.lean#L49-L94

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {R₀ R : Type} [CommRing R₀] [CommRing R] {X Y : Scheme.{0}}
  (f₀ : X ⟶ Spec (CommRingCat.of R₀))
variable {f₀}

theorem GlobalTheory.CompanionTheory.Ultra.val_lift {φ : R₀ →+* R} {f : Y ⟶ Spec (CommRingCat.of R)} {π : Y ⟶ X}
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (hval : ValuativeCriterion f)
    {B L : Type} [CommRing B] [IsDomain B] [ValuationRing B] [Field L] [Algebra B L]
    [IsFractionRing B L] (ρ : R →+* B) (a₀ : Spec (CommRingCat.of L) ⟶ X)
    (H : a₀ ≫ f₀ = Spec.map (CommRingCat.ofHom ((algebraMap B L).comp (ρ.comp φ)))) :
    (∃ ℓ : Spec (CommRingCat.of B) ⟶ X, ℓ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ = a₀) ∧
    ∀ ℓ₁ ℓ₂ : Spec (CommRingCat.of B) ⟶ X,
      ℓ₁ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) →
      ℓ₂ ≫ f₀ = Spec.map (CommRingCat.ofHom (ρ.comp φ)) →
      Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ₁ = a₀ →
      Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ ℓ₂ = a₀ → ℓ₁ = ℓ₂ := by sorry
