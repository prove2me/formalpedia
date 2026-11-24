-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_mul_le
-- name    : FunctorialResolution.EmbeddedResolution.derivIdeal_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:48.36325+00:00
-- url     : https://prove2.me/theorems/8060729a-6987-48e8-a043-c40ac17d92b2
-- title:
--   Embedded Resolution: deriv Ideal mul le
-- statement:
--   The Embedded Resolution construction uses the deriv Ideal mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L92-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L92-L111

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

theorem FunctorialResolution.EmbeddedResolution.derivIdeal_mul_le (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (I J : Ideal S) :
    derivIdeal k (I * J) ≤ I * derivIdeal k J ⊔ J * derivIdeal k I := by sorry
