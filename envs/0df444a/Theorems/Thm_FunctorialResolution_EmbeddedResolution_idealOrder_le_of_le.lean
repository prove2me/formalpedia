-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_le_of_le
-- name    : FunctorialResolution.EmbeddedResolution.idealOrder_le_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:19.344935+00:00
-- url     : https://prove2.me/theorems/5c0f24fe-29a7-4dbf-9157-23f515409930
-- title:
--   Embedded Resolution: ideal Order le of le
-- statement:
--   The Embedded Resolution construction uses the ideal Order le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L104-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L104-L113

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

theorem FunctorialResolution.EmbeddedResolution.idealOrder_le_of_le {I J : Ideal R} (h : I ≤ J) : idealOrder J ≤ idealOrder I := by sorry
