-- Prove2me | Theorems.Thm_GlobalTheory_DenseFibreIso_includeLeft_eq
-- name    : GlobalTheory.DenseFibreIso.includeLeft_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:19:27.288702+00:00
-- url     : https://prove2.me/theorems/f3e006a0-0f23-4c0d-8846-9a658bad586c
-- title:
--   Dense Fibre Iso: include Left eq
-- statement:
--   The Dense Fibre Iso construction uses the include Left eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAwaySurjective.lean#L51-L55

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

theorem GlobalTheory.DenseFibreIso.includeLeft_eq (S : Type) [CommRing S] [Algebra A S] :
    ⇑(Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B) =
      (Algebra.linearMap A B).lTensor S ∘ (TensorProduct.rid A S).symm := by sorry
