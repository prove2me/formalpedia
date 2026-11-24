-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_one_le_idealOrder_iff_ne_top
-- name    : FunctorialResolution.EmbeddedResolution.one_le_idealOrder_iff_ne_top
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:48:51.082859+00:00
-- url     : https://prove2.me/theorems/0f161ee4-9f73-4016-891a-6c0a054424f7
-- title:
--   Embedded Resolution: one le ideal Order iff ne top
-- statement:
--   The Embedded Resolution construction uses the one le ideal Order iff ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L60-L68

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

theorem FunctorialResolution.EmbeddedResolution.one_le_idealOrder_iff_ne_top (I : Ideal R) :
    1 ≤ idealOrder I ↔ I ≠ ⊤ := by sorry
