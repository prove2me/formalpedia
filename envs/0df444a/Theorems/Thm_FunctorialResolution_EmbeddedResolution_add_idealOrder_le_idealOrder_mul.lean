-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_add_idealOrder_le_idealOrder_mul
-- name    : FunctorialResolution.EmbeddedResolution.add_idealOrder_le_idealOrder_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:46:58.716546+00:00
-- url     : https://prove2.me/theorems/7b8d2872-28a9-4a57-af00-c22c85acd74e
-- title:
--   Embedded Resolution: add ideal Order le ideal Order mul
-- statement:
--   The Embedded Resolution construction uses the add ideal Order le ideal Order mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L149-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L149-L154

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

theorem FunctorialResolution.EmbeddedResolution.add_idealOrder_le_idealOrder_mul (I J : Ideal R) :
    idealOrder I + idealOrder J ≤ idealOrder (I * J) := by sorry
