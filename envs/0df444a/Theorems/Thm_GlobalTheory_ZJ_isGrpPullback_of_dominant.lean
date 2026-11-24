-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_isGrpPullback_of_dominant
-- name    : GlobalTheory.ZJ.isGrpPullback_of_dominant
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:03:10.261445+00:00
-- url     : https://prove2.me/theorems/c75f7d13-e762-4134-b263-e2e1b9df1ae4
-- title:
--   ZJ: is Grp Pullback of dominant
-- statement:
--   The ZJ construction uses the is Grp Pullback of dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NonemptyLawAbelianSchemeProperClosure.lean#L18-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NonemptyLawAbelianSchemeProperClosure.lean#L18-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NonemptyLawAbelianSchemeProperClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ

theorem GlobalTheory.ZJ.isGrpPullback_of_dominant {W S Z : Scheme.{0}} (j : W ⟶ S) [QuasiCompact j]
    [IsSchemeTheoreticallyDominant j] {H : Over S} [GrpObj H] [Flat H.hom] {G : Over Z} [GrpObj G]
    [IsSeparated G.hom] {y : S ⟶ Z} {f : H.left ⟶ G.left} (hf : IsPullback f H.hom G.hom y)
    (h : IsGrpPullback ((Over.pullback j).obj H) G (j ≫ y) (pullback.fst H.hom j ≫ f)) :
    IsGrpPullback H G y f := by sorry
