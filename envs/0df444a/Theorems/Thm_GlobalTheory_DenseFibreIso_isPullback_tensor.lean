-- Prove2me | Theorems.Thm_GlobalTheory_DenseFibreIso_isPullback_tensor
-- name    : GlobalTheory.DenseFibreIso.isPullback_tensor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:44.873177+00:00
-- url     : https://prove2.me/theorems/75a4d987-f67b-4fd5-bb9e-071a786d427c
-- title:
--   Dense Fibre Iso: is Pullback tensor
-- statement:
--   The Dense Fibre Iso construction uses the is Pullback tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L178-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L178-L183

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

theorem GlobalTheory.DenseFibreIso.isPullback_tensor (A S B : Type) [CommRing A] [CommRing S] [CommRing B] [Algebra A S]
    [Algebra A B] :
    IsPullback (spMap (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B))
      (spMap (Algebra.TensorProduct.includeRight.toRingHom : B →+* S ⊗[A] B))
      (spMap (algebraMap A S)) (spMap (algebraMap A B)) := by sorry
