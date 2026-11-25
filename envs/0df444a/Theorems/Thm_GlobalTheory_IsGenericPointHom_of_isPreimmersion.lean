-- Prove2me | Theorems.Thm_GlobalTheory_IsGenericPointHom_of_isPreimmersion
-- name    : GlobalTheory.IsGenericPointHom.of_isPreimmersion
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:33.121815+00:00
-- url     : https://prove2.me/theorems/b5364a40-d7c0-4fd4-a942-83a66929ec17
-- title:
--   Is Generic Point Hom: of is Preimmersion
-- statement:
--   The Is Generic Point Hom construction uses the of is Preimmersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L191-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L191-L221

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
open GlobalTheory
open ExtUnique
open GlobalTheory.IsGenericPointHom

theorem GlobalTheory.IsGenericPointHom.of_isPreimmersion {S : Scheme.{u}} [IsIntegral S] {K : Type u} [Field K] (j : Spec (.of K) ⟶ S)
    [IsPreimmersion j] [IsDominant j] : IsGenericPointHom j := by sorry
