-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdeal
-- name    : FunctorialResolution.EmbeddedResolution.le_derivIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:39.680167+00:00
-- url     : https://prove2.me/theorems/53528d9e-d65e-4fc5-8d93-5d4d6bf528ff
-- title:
--   Embedded Resolution: le deriv Ideal
-- statement:
--   The Embedded Resolution construction uses the le deriv Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L27-L30

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

theorem FunctorialResolution.EmbeddedResolution.le_derivIdeal (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (J : Ideal S) : J ≤ derivIdeal k J := by sorry
