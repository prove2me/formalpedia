-- Prove2me | Theorems.Thm_GlobalTheory_DenseFibreIso_exists_away_bijective
-- name    : GlobalTheory.DenseFibreIso.exists_away_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:19:33.123027+00:00
-- url     : https://prove2.me/theorems/096c9b6c-a62a-4cf1-95c9-67e118ba6778
-- title:
--   Dense Fibre Iso: exists away bijective
-- statement:
--   The Dense Fibre Iso construction uses the exists away bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L84-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L84-L122

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

theorem GlobalTheory.DenseFibreIso.exists_away_bijective [IsNoetherianRing A] (R K : Type) [CommRing R] [CommRing K]
    [Algebra R K] [Algebra R A] [Algebra R B] [IsScalarTower R A B] [Module.Flat R B]
    (hs : Function.Surjective (algebraMap A B))
    (h : Function.Injective
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))
    (m : PrimeSpectrum (A ⊗[R] K)) :
    ∃ a : A, algebraMap A (A ⊗[R] K) a ∉ m.asIdeal ∧ Function.Bijective
      (Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away a →+* Localization.Away a ⊗[A] B) := by sorry
