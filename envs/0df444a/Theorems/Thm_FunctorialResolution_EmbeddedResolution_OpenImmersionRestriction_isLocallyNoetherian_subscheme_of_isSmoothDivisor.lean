-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isLocallyNoetherian_subscheme_of_isSmoothDivisor
-- name    : FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.isLocallyNoetherian_subscheme_of_isSmoothDivisor
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:33:09.933627+00:00
-- url     : https://prove2.me/theorems/bde5bb81-2a13-48cb-a9e1-8db8dc6dd107
-- title:
--   Open Immersion Restriction: is Locally Noetherian subscheme of is Smooth Divisor
-- statement:
--   The Open Immersion Restriction construction uses the is Locally Noetherian subscheme of is Smooth Divisor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealOrderOne.lean#L129-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/VanishingIdealOrderOne.lean#L129-L138

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

theorem FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.isLocallyNoetherian_subscheme_of_isSmoothDivisor
    (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    (U : W.Opens) (D : (U.toScheme).IdealSheafData)
    (hD : IsSmoothDivisor (U.ι ≫ p) D) :
    IsLocallyNoetherian D.subscheme := by sorry
