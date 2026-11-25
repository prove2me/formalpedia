-- Prove2me | Theorems.Thm_GlobalTheory_IsGenericPointHom_fractionField
-- name    : GlobalTheory.IsGenericPointHom.fractionField
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:16:35.117965+00:00
-- url     : https://prove2.me/theorems/38dbc5cc-08ed-4b57-8826-e3ec75db18b5
-- title:
--   Is Generic Point Hom: fraction Field
-- statement:
--   The Is Generic Point Hom construction uses the fraction Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L223-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L223-L235

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

theorem GlobalTheory.IsGenericPointHom.fractionField (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :
    IsGenericPointHom (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by sorry
