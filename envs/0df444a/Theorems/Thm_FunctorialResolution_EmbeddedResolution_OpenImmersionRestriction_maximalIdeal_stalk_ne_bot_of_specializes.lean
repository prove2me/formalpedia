-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_maximalIdeal_stalk_ne_bot_of_specializes
-- name    : FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.maximalIdeal_stalk_ne_bot_of_specializes
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:33:05.149749+00:00
-- url     : https://prove2.me/theorems/7fd8683e-921a-4acd-b16f-27d72612fa1c
-- title:
--   Open Immersion Restriction: maximal Ideal stalk ne bot of specializes
-- statement:
--   The Open Immersion Restriction construction uses the maximal Ideal stalk ne bot of specializes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealOrderOne.lean#L19-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealOrderOne.lean#L19-L82

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

theorem FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.maximalIdeal_stalk_ne_bot_of_specializes
    (X : Scheme.{u}) (x y : ↥X) (h : y ⤳ x) (hne : y ≠ x) :
    IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ≠ ⊥ := by sorry
