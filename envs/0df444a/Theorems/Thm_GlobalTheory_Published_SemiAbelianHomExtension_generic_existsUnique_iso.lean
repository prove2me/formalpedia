-- Prove2me | Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_generic_existsUnique_iso
-- name    : GlobalTheory.Published.SemiAbelianHomExtension.generic_existsUnique_iso
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:17:19.372192+00:00
-- url     : https://prove2.me/theorems/649ff90f-3fe9-4399-8ece-3fd19fd4e43a
-- title:
--   Semi Abelian Hom Extension: generic exists Unique iso
-- statement:
--   The Semi Abelian Hom Extension construction uses the generic exists Unique iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L551-L558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L551-L558

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {j : U ⟶ S}

theorem GlobalTheory.Published.SemiAbelianHomExtension.generic_existsUnique_iso (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (hj : IsGenericPointHom j) {G H : Over S} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (e : (Over.pullback j).obj G ≅ (Over.pullback j).obj H)
    [IsMonHom e.hom] : ∃! E : G ≅ H, IsMonHom E.hom ∧ (Over.pullback j).map E.hom = e.hom := by sorry
