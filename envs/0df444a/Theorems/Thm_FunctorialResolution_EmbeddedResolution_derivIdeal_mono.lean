-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_mono
-- name    : FunctorialResolution.EmbeddedResolution.derivIdeal_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:53.116799+00:00
-- url     : https://prove2.me/theorems/16803ee4-f26f-4d71-90f2-0b426debd6a4
-- title:
--   Embedded Resolution: deriv Ideal mono
-- statement:
--   The Embedded Resolution construction uses the deriv Ideal mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L50-L54

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

theorem FunctorialResolution.EmbeddedResolution.derivIdeal_mono (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S] :
    Monotone (derivIdeal k : Ideal S → Ideal S) := by sorry
