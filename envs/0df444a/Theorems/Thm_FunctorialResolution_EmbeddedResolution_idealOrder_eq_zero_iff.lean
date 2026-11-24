-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_eq_zero_iff
-- name    : FunctorialResolution.EmbeddedResolution.idealOrder_eq_zero_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:47:40.561895+00:00
-- url     : https://prove2.me/theorems/c009a97e-b5b4-4bd1-8800-f6057899794d
-- title:
--   Embedded Resolution: ideal Order eq zero iff
-- statement:
--   The Embedded Resolution construction uses the ideal Order eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L70-L72

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

theorem FunctorialResolution.EmbeddedResolution.idealOrder_eq_zero_iff (I : Ideal R) :
    idealOrder I = 0 ↔ ¬ I ≤ IsLocalRing.maximalIdeal R := by sorry
