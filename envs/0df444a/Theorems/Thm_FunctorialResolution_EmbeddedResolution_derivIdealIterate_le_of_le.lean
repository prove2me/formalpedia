-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_le_of_le
-- name    : FunctorialResolution.EmbeddedResolution.derivIdealIterate_le_of_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:14.03689+00:00
-- url     : https://prove2.me/theorems/8cf4679f-12d5-46d9-9de6-38255a7f4ab8
-- title:
--   Embedded Resolution: deriv Ideal Iterate le of le
-- statement:
--   The Embedded Resolution construction uses the deriv Ideal Iterate le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L247-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L247-L252

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

theorem FunctorialResolution.EmbeddedResolution.derivIdealIterate_le_of_le (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    {r r' : ℕ} (h : r ≤ r') (J : Ideal S) :
    derivIdealIterate k r J ≤ derivIdealIterate k r' J := by sorry
