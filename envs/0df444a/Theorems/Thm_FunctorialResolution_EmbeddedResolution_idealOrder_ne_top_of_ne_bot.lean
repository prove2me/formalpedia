-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_ne_top_of_ne_bot
-- name    : FunctorialResolution.EmbeddedResolution.idealOrder_ne_top_of_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:33.141372+00:00
-- url     : https://prove2.me/theorems/cdcf6526-8b92-46ca-b96b-73a78c5593de
-- title:
--   Embedded Resolution: ideal Order ne top of ne bot
-- statement:
--   The Embedded Resolution construction uses the ideal Order ne top of ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L87-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L87-L97

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

theorem FunctorialResolution.EmbeddedResolution.idealOrder_ne_top_of_ne_bot [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊥) :
    idealOrder I ≠ ⊤ := by sorry
