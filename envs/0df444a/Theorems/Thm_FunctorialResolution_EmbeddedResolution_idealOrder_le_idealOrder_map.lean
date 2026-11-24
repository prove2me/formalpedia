-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_le_idealOrder_map
-- name    : FunctorialResolution.EmbeddedResolution.idealOrder_le_idealOrder_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:25:37.690466+00:00
-- url     : https://prove2.me/theorems/07d50cea-1131-41de-8887-fe72907d306f
-- title:
--   Embedded Resolution: ideal Order le ideal Order map
-- statement:
--   The Embedded Resolution construction uses the ideal Order le ideal Order map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L193-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L193-L198

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

theorem FunctorialResolution.EmbeddedResolution.idealOrder_le_idealOrder_map (f : R →+* S)
    (hf : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S) (I : Ideal R) :
    idealOrder I ≤ idealOrder (I.map f) := by sorry
