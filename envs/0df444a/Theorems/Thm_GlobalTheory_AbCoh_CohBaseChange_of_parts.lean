-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_CohBaseChange_of_parts
-- name    : GlobalTheory.AbCoh.CohBaseChange.of_parts
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:05:04.238943+00:00
-- url     : https://prove2.me/theorems/81eccba0-4c25-41e3-aec9-d60c353185f0
-- title:
--   Coh Base Change: of parts
-- statement:
--   The Coh Base Change construction uses the of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpMapAlgHomAlgebraMap.lean#L100-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpMapAlgHomAlgebraMap.lean#L100-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpMapAlgHomAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.CohBaseChange
variable {R : Type} [CommRing R]
variable {X : Scheme.{0}} {s : X ⟶ Sp R} {K : CochainComplex (ModuleCat.{0} R) ℕ}

theorem GlobalTheory.AbCoh.CohBaseChange.of_parts (hex : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ (∃ n, ∀ p, n < p → IsZero (K.X p)) ∧ Nonempty (Model s K))
    (halg : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∃ n, ∀ p, n < p → IsZero (K.X p)) → (∀ i, i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → LiftsAt K α i) → ∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom))
    (hsplit : ∀ (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom)) → ∀ i, 1 ≤ i → i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'], ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Finite R P) (_ : Module.Projective R P) (u : LinearMap.ker (dB K R i (i + 1)) →ₗ[R] P) (v : LinearMap.ker (dB K R' i (i + 1)) →ₗ[R'] R' ⊗[R] P), Function.Surjective u ∧ Function.Surjective v ∧ (∀ z, u z = 0 ↔ z.1 ∈ LinearMap.range (dB K R (i - 1) i)) ∧ (∀ z, v z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' (i - 1) i)) ∧ ∀ z z', z'.1 = ext (Algebra.ofId R R') _ z.1 → v z' = 1 ⊗ₜ u z) :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s := by sorry
