-- Prove2me | Theorems.Thm_GlobalTheory_TorusToProper_point_extend
-- name    : GlobalTheory.TorusToProper.point_extend
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:11:06.971751+00:00
-- url     : https://prove2.me/theorems/3105ce90-77b3-429b-9059-684f94a1c559
-- title:
--   Torus To Proper: point extend
-- statement:
--   The Torus To Proper construction uses the point extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialField.lean#L53-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialField.lean#L53-L65

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

theorem GlobalTheory.TorusToProper.point_extend {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Algebra K V] [Field F]
    [Algebra K F] [Algebra V F] [IsScalarTower K V F] [IsFractionRing V F]
    {B : Over (Spec (CommRingCat.of K))} [IsProper B.hom] (p : sp K F ⟶ B) :
    ∃ b : sp K V ⟶ B, spm (IsScalarTower.toAlgHom K V F) ≫ b = p := by sorry
