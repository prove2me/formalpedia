-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isOpen_setOf_stalkIdeal_eq_bot
-- name    : FunctorialResolution.EmbeddedResolution.isOpen_setOf_stalkIdeal_eq_bot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:31:03.696868+00:00
-- url     : https://prove2.me/theorems/1f895b67-c27c-425e-8ada-fe9befa74f8b
-- title:
--   Embedded Resolution: is Open set Of stalk Ideal eq bot
-- statement:
--   The Embedded Resolution construction uses the is Open set Of stalk Ideal eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/LocallyBoundedOrder.lean#L16-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/LocallyBoundedOrder.lean#L16-L72

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_LocallyBoundedOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.isOpen_setOf_stalkIdeal_eq_bot {X : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (J : X.IdealSheafData) :
    IsOpen {x : ↥X | stalkIdeal J x = (⊥ : Ideal (X.presheaf.stalk x))} := by sorry
