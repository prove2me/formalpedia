-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_orderAt_vanishingIdeal_eq_one_of_not_mem_irreducibleComponents
-- name    : FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.orderAt_vanishingIdeal_eq_one_of_not_mem_irreducibleComponents
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:33:12.159235+00:00
-- url     : https://prove2.me/theorems/3beeba54-b14c-4cdc-b3e3-e84c76061fc7
-- title:
--   Open Immersion Restriction: order At vanishing Ideal eq one of not mem irreducible Components
-- statement:
--   The Open Immersion Restriction construction uses the order At vanishing Ideal eq one of not mem irreducible Components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealOrderOne.lean#L84-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealOrderOne.lean#L84-L127

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

theorem FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.orderAt_vanishingIdeal_eq_one_of_not_mem_irreducibleComponents
    (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Closeds ↥X) (x : ↥X)
    (hx : IsGenericPoint x (S : Set ↥X))
    (hS : (S : Set ↥X) ∉ irreducibleComponents ↥X) :
    FunctorialResolution.EmbeddedResolution.orderAt (Scheme.IdealSheafData.vanishingIdeal S) x = 1 := by sorry
