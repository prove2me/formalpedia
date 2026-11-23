-- Prove2me | Theorems.Thm_GlobalTheory_DenseFibreIso_exists_away_surjective
-- name    : GlobalTheory.DenseFibreIso.exists_away_surjective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:18:48.940839+00:00
-- url     : https://prove2.me/theorems/05340f48-4cad-48cf-8755-9940a6deb52c
-- title:
--   Dense Fibre Iso: exists away surjective
-- statement:
--   The Dense Fibre Iso construction uses the exists away surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L72-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L72-L82

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
variable {A : Type} [CommRing A]
variable {B : Type} [CommRing B] [Algebra A B]

theorem GlobalTheory.DenseFibreIso.exists_away_surjective [Module.Finite A B] (A' : Type) [CommRing A'] [Algebra A A']
    (h : Function.Surjective (Algebra.TensorProduct.includeLeftRingHom : A' →+* A' ⊗[A] B))
    (m : PrimeSpectrum A') :
    ∃ a : A, algebraMap A A' a ∉ m.asIdeal ∧ Function.Surjective
      (Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away a →+* Localization.Away a ⊗[A] B) := by sorry
