-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_sup
-- name    : FunctorialResolution.EmbeddedResolution.idealOrder_sup
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:47:43.532804+00:00
-- url     : https://prove2.me/theorems/7037b5e9-d551-4901-a42f-aca06701e97f
-- title:
--   Embedded Resolution: ideal Order sup
-- statement:
--   The Embedded Resolution construction uses the ideal Order sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L115-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L115-L124

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

theorem FunctorialResolution.EmbeddedResolution.idealOrder_sup (I J : Ideal R) :
    idealOrder (I ⊔ J) = min (idealOrder I) (idealOrder J) := by sorry
