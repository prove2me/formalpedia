-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isMonomialSplitting_comap_of_generalizingMap
-- name    : FunctorialResolution.EmbeddedResolution.isMonomialSplitting_comap_of_generalizingMap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:07:21.343622+00:00
-- url     : https://prove2.me/theorems/da9928ad-84d5-4033-8f70-10a1e2f3c5a4
-- title:
--   Embedded Resolution: is Monomial Splitting comap of generalizing Map
-- statement:
--   The Embedded Resolution construction uses the is Monomial Splitting comap of generalizing Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/MonomialSplittingFlatPullback.lean#L131-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/MonomialSplittingFlatPullback.lean#L131-L139

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplittingFlatPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X Y : Scheme.{u}}

theorem FunctorialResolution.EmbeddedResolution.isMonomialSplitting_comap_of_generalizingMap (h : Y ⟶ X)
    (hg : GeneralizingMap (fun y : Y => h.base y)) {E : List X.IdealSheafData}
    {I M N : X.IdealSheafData} (hs : IsMonomialSplitting E I M N) :
    IsMonomialSplitting (E.map (fun D : X.IdealSheafData => D.comap h)) (I.comap h) (M.comap h)
      (N.comap h) := by sorry
