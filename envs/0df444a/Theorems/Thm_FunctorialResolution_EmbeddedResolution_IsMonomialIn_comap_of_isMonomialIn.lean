-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsMonomialIn_comap_of_isMonomialIn
-- name    : FunctorialResolution.EmbeddedResolution.IsMonomialIn.comap_of_isMonomialIn
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:07:11.126461+00:00
-- url     : https://prove2.me/theorems/9d216998-f40a-49a3-8153-1618d384ad11
-- title:
--   Is Monomial In: comap of is Monomial In
-- statement:
--   The Is Monomial In construction uses the comap of is Monomial In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/MonomialSplittingFlatPullback.lean#L37-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/MonomialSplittingFlatPullback.lean#L37-L62

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

theorem FunctorialResolution.EmbeddedResolution.IsMonomialIn.comap_of_isMonomialIn {E : List X.IdealSheafData} {M : X.IdealSheafData}
    (hM : IsMonomialIn E M) (h : Y ⟶ X) :
    IsMonomialIn (E.map (fun D : X.IdealSheafData => D.comap h)) (M.comap h) := by sorry
