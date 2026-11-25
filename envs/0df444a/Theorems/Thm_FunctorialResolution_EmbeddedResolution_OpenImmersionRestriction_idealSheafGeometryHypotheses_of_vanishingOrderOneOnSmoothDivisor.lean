-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_idealSheafGeometryHypotheses_of_vanishingOrderOneOnSmoothDivisor
-- name    : FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.idealSheafGeometryHypotheses_of_vanishingOrderOneOnSmoothDivisor
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:36.612933+00:00
-- url     : https://prove2.me/theorems/fb3006b7-b7f2-5c0d-976e-2e70598ae5df
-- title:
--   Open Immersion Restriction: ideal Sheaf Geometry Hypotheses of vanishing Order One On Smooth Divisor
-- statement:
--   The Open Immersion Restriction construction uses the ideal Sheaf Geometry Hypotheses of vanishing Order One On Smooth Divisor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealAssignment.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealAssignment.lean#L108-L112

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

theorem FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.idealSheafGeometryHypotheses_of_vanishingOrderOneOnSmoothDivisor
    (h1 : VanishingOrderOneOnSmoothDivisor.{u}) (h2 : AgreeNearVanishingComapSubscheme.{u})
    (h3 : VanishingComapOpens.{u}) :
    IdealSheafGeometryHypotheses vanishingIdealAssignment.{u} := by sorry
