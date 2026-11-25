-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_vanishingOrderOneOnSmoothDivisor
-- name    : FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.vanishingOrderOneOnSmoothDivisor
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:55:31.902553+00:00
-- url     : https://prove2.me/theorems/bee29b18-fb7a-5874-8b48-ebba0d0d00b9
-- title:
--   Open Immersion Restriction: vanishing Order One On Smooth Divisor
-- statement:
--   The Open Immersion Restriction construction uses the vanishing Order One On Smooth Divisor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealOrderOne.lean#L140-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealOrderOne.lean#L140-L145

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealAssignment
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealOrderOne
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

theorem FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.vanishingOrderOneOnSmoothDivisor : VanishingOrderOneOnSmoothDivisor.{u} := by sorry
