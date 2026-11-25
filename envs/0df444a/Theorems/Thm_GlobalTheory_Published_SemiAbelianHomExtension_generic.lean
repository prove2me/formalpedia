-- Prove2me | Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_generic
-- name    : GlobalTheory.Published.SemiAbelianHomExtension.generic
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:16:54.759074+00:00
-- url     : https://prove2.me/theorems/959fa53b-1f4b-4118-a1b6-bbe32d3e7616
-- title:
--   Semi Abelian Hom Extension: generic
-- statement:
--   The Semi Abelian Hom Extension construction uses the generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L595-L599
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L595-L599

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

theorem GlobalTheory.Published.SemiAbelianHomExtension.generic (h : GlobalTheory.Published.SemiAbelianHomExtension) (S : Scheme.{0}) [IsIntegral S] [AlgebraicGeometry.IsNoetherian S]
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (G H : Over S) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (f : (Over.pullback (S.fromSpecStalk (genericPoint S))).obj G ⟶ (Over.pullback (S.fromSpecStalk (genericPoint S))).obj H) [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (S.fromSpecStalk (genericPoint S))).map F = f := by sorry
