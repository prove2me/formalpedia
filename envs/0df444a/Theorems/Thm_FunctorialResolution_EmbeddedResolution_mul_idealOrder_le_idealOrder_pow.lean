-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mul_idealOrder_le_idealOrder_pow
-- name    : FunctorialResolution.EmbeddedResolution.mul_idealOrder_le_idealOrder_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:48:06.97492+00:00
-- url     : https://prove2.me/theorems/586ec879-131c-4227-91c2-0aa8d1681d33
-- title:
--   Embedded Resolution: mul ideal Order le ideal Order pow
-- statement:
--   The Embedded Resolution construction uses the mul ideal Order le ideal Order pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L156-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L156-L178

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

theorem FunctorialResolution.EmbeddedResolution.mul_idealOrder_le_idealOrder_pow (I : Ideal R) (c : ℕ) :
    (c : ℕ∞) * idealOrder I ≤ idealOrder (I ^ c) := by sorry
