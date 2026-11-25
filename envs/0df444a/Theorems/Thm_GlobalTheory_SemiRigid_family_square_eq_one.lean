-- Prove2me | Theorems.Thm_GlobalTheory_SemiRigid_family_square_eq_one
-- name    : GlobalTheory.SemiRigid.family_square_eq_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:28:45.435509+00:00
-- url     : https://prove2.me/theorems/dbeaac22-77e4-49e2-be8c-71b159dab32e
-- title:
--   Semi Rigid: family square eq one
-- statement:
--   The Semi Rigid construction uses the family square eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsTorusAndQuotientHom.lean#L447-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsTorusAndQuotientHom.lean#L447-L461

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqCompSectionOfSurjectiveAppTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SurjectiveAppOfIsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GroupRingHomConstOfLaurent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SemiRigid
open SplitTorus
variable {S : Scheme.{0}}

theorem GlobalTheory.SemiRigid.family_square_eq_one [IsReduced S] {G H : Over S} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (f : G ⊗ G ⟶ H) (h₁ : lift (𝟙 G) 1 ≫ f = 1)
    (h₂ : lift 1 (𝟙 G) ≫ f = 1) : f = 1 := by sorry
