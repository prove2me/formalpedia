-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal
-- name    : FunctorialResolution.EmbeddedResolution.derivation_apply_mem_derivIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:38.796902+00:00
-- url     : https://prove2.me/theorems/bc826993-e7a0-47a0-9ee4-38e416c3f95c
-- title:
--   Embedded Resolution: derivation apply mem deriv Ideal
-- statement:
--   The Embedded Resolution construction uses the derivation apply mem deriv Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L32-L36

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.derivation_apply_mem_derivIdeal (k : Type*) [CommRing k] {S : Type*} [CommRing S]
    [Algebra k S] (J : Ideal S) (D : Derivation k S S) {x : S} (hx : x ∈ J) :
    D x ∈ derivIdeal k J := by sorry
