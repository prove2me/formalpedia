-- Prove2me | Theorems.Thm_GlobalTheory_TorusToProper_point_ext
-- name    : GlobalTheory.TorusToProper.point_ext
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:47:11.713042+00:00
-- url     : https://prove2.me/theorems/15afeeb9-cc7f-4c87-99e5-6ee7684f0748
-- title:
--   Torus To Proper: point ext
-- statement:
--   The Torus To Proper construction uses the point ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialField.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialField.lean#L40-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusToProper
variable {K : Type} [Field K]

theorem GlobalTheory.TorusToProper.point_ext {V F : Type} [CommRing V] [IsDomain V] [Algebra K V] [CommRing F] [Algebra K F]
    (j : V →ₐ[K] F) (hj : Function.Injective j)
    {B : Over (Spec (CommRingCat.of K))} [IsSeparated B.hom] {b b' : sp K V ⟶ B}
    (h : spm j ≫ b = spm j ≫ b') : b = b' := by sorry
