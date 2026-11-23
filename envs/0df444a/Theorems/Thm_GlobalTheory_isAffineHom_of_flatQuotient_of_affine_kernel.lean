-- Prove2me | Theorems.Thm_GlobalTheory_isAffineHom_of_flatQuotient_of_affine_kernel
-- name    : GlobalTheory.isAffineHom_of_flatQuotient_of_affine_kernel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:13.628377+00:00
-- url     : https://prove2.me/theorems/de7e0bcc-4a32-4368-8b37-267885dc0ccf
-- title:
--   Global Theory: is Affine Hom of flat Quotient of affine kernel
-- statement:
--   The Global Theory construction uses the is Affine Hom of flat Quotient of affine kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomOfFlatQuotientOfAffineKernel.lean#L155-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomOfFlatQuotientOfAffineKernel.lean#L155-L177

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.isAffineHom_of_flatQuotient_of_affine_kernel :
    ∀ (S : Scheme.{0}) (G B T : Over S) [GrpObj G] [GrpObj B] [GrpObj T] (q : G ⟶ B) (i : T ⟶ G),
      IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left →
      IsPullback i (toUnit _) q (η[B]) → IsAffineHom T.hom → IsAffineHom q.left := by sorry
