-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_map_eq_of_comp_eq_id
-- name    : FunctorialResolution.EmbeddedResolution.idealOrder_map_eq_of_comp_eq_id
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:12:35.312221+00:00
-- url     : https://prove2.me/theorems/09a0fb1f-9d67-426b-990d-41e7c40562d1
-- title:
--   Embedded Resolution: ideal Order map eq of comp eq id
-- statement:
--   The Embedded Resolution construction uses the ideal Order map eq of comp eq id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/OrderUnderStalkIsomorphism.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/OrderUnderStalkIsomorphism.lean#L33-L42

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_OrderUnderStalkIsomorphism
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.idealOrder_map_eq_of_comp_eq_id {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (f : R →+* S) (g : S →+* R)
    (hgf : g.comp f = RingHom.id R) (hfg : f.comp g = RingHom.id S) (I : Ideal R) :
    idealOrder (Ideal.map f I) = idealOrder I := by sorry
