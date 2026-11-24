-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_idealSheafGeometryHypotheses_of_orderAtEqOfAgreeNear
-- name    : FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.idealSheafGeometryHypotheses_of_orderAtEqOfAgreeNear
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:13:55.73203+00:00
-- url     : https://prove2.me/theorems/a90d1d92-bdb2-4c8c-9bdf-1901087f6a63
-- title:
--   Open Immersion Restriction: ideal Sheaf Geometry Hypotheses of order At Eq Of Agree Near
-- statement:
--   The Open Immersion Restriction construction uses the ideal Sheaf Geometry Hypotheses of order At Eq Of Agree Near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealAssignment.lean#L76-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealAssignment.lean#L76-L106

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealAssignment
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

theorem FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.idealSheafGeometryHypotheses_of_orderAtEqOfAgreeNear
    (h1 : VanishingOrderOneOnSmoothDivisor.{u}) (h2 : AgreeNearVanishingComapSubscheme.{u})
    (h3 : VanishingComapOpens.{u}) (h4 : OrderAtEqOfAgreeNear.{u}) :
    IdealSheafGeometryHypotheses vanishingIdealAssignment.{u} := by sorry
