-- Prove2me | Theorems.Thm_GlobalTheory_SemiRigid_affine_eq_one
-- name    : GlobalTheory.SemiRigid.affine_eq_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:26:42.434902+00:00
-- url     : https://prove2.me/theorems/f0ddf942-cc39-4898-a2e0-314855038155
-- title:
--   Semi Rigid: affine eq one
-- statement:
--   The Semi Rigid construction uses the affine eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsTorusAndQuotientHom.lean#L102-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsTorusAndQuotientHom.lean#L102-L130

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
variable {R : CommRingCat.{0}} (X : Type) [AddCommGroup X] (t : Spec R ⟶ S)
variable [Module.Free ℤ X] [Module.Finite ℤ X] [IsDomain R]

theorem GlobalTheory.SemiRigid.affine_eq_one {H B : Over S} [GrpObj H] [GrpObj B] [IsProper B.hom] {Y : Type}
    [AddCommGroup Y] (i : splitTorus S Y ⟶ H) (q : H ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q η[B]) (d : grpSpec X t ⟶ H) (h₁ : unitSec X t ≫ d = 1)
    {L : CommRingCat.{0}} [Nontrivial L] (ρ : R ⟶ L) {s : Spec (torusRing L X) ⟶ S}
    (hs : Spec.map (CommRingCat.ofHom (R := torusRing R X) (S := torusRing L X)
      (AddMonoidAlgebra.mapRingHom X ρ.hom)) ≫ (grpSpec X t).hom = s)
    (h₂ : sp _ hs ≫ d = 1) : d = 1 := by sorry
