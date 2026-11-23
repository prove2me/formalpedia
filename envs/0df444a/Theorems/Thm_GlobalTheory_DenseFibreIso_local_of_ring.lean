-- Prove2me | Theorems.Thm_GlobalTheory_DenseFibreIso_local_of_ring
-- name    : GlobalTheory.DenseFibreIso.local_of_ring
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:18:34.053811+00:00
-- url     : https://prove2.me/theorems/8fbfc493-4c48-4180-9d64-7dbab7e85029
-- title:
--   Dense Fibre Iso: local of ring
-- statement:
--   The Dense Fibre Iso construction uses the local of ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L185-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L185-L219

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.DenseFibreIso
variable {R : Type} [CommRing R] {Γ' X : Scheme.{0}} (s : X ⟶ Sp R) (f : Γ' ⟶ X)

theorem GlobalTheory.DenseFibreIso.local_of_ring [IsAffineHom f] (Q : MorphismProperty Scheme.{0}) (K : Type) [Field K]
    [Algebra R K] [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (h : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
      [IsScalarTower R A B] (j : Sp A ⟶ X) (j' : Sp B ⟶ Γ') [IsOpenImmersion j],
      IsPullback (spMap (algebraMap A B)) j' j f → j ≫ s = spMap (algebraMap R A) →
      Function.Bijective
        (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B) →
      ∀ m : PrimeSpectrum (A ⊗[R] K), ∃ a : A, algebraMap A (A ⊗[R] K) a ∉ m.asIdeal ∧
        Q (spMap (Algebra.TensorProduct.includeLeftRingHom :
          Localization.Away a →+* Localization.Away a ⊗[A] B)))
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    ∃ (T T' : Scheme.{0}) (g : T ⟶ X) (g' : T' ⟶ Γ')
      (f' : T' ⟶ T), IsPullback f' g' g f ∧ IsOpenImmersion g ∧ x ∈ Set.range g ∧ Q f' := by sorry
