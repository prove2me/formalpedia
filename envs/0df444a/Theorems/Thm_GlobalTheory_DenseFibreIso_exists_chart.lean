-- Prove2me | Theorems.Thm_GlobalTheory_DenseFibreIso_exists_chart
-- name    : GlobalTheory.DenseFibreIso.exists_chart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:59.997608+00:00
-- url     : https://prove2.me/theorems/55b804a8-76a7-4b40-a28a-9cdaf7ec21dd
-- title:
--   Dense Fibre Iso: exists chart
-- statement:
--   The Dense Fibre Iso construction uses the exists chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L164-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L164-L176

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

theorem GlobalTheory.DenseFibreIso.exists_chart [IsAffineHom f] (x : X) :
    ∃ (A B : CommRingCat.{0}) (ψ : CommRingCat.of R ⟶ A) (φ : A ⟶ B) (j : Spec A ⟶ X)
      (j' : Spec B ⟶ Γ'), IsOpenImmersion j ∧ x ∈ Set.range j ∧
        IsPullback (Spec.map φ) j' j f ∧ j ≫ s = Spec.map ψ := by sorry
