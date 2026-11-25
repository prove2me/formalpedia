-- Prove2me | Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_of_isGenericPointHom
-- name    : GlobalTheory.Published.SemiAbelianHomExtension.of_isGenericPointHom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:17:26.405011+00:00
-- url     : https://prove2.me/theorems/4b24fc16-cdd9-4743-b71f-014b64c2a7f1
-- title:
--   Semi Abelian Hom Extension: of is Generic Point Hom
-- statement:
--   The Semi Abelian Hom Extension construction uses the of is Generic Point Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L523-L529
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L523-L529

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

theorem GlobalTheory.Published.SemiAbelianHomExtension.of_isGenericPointHom (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (hj : IsGenericPointHom j) {G H : Over S} [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H) [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback j).map F = f := by sorry
