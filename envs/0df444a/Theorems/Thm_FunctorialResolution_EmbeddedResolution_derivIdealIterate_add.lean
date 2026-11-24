-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_add
-- name    : FunctorialResolution.EmbeddedResolution.derivIdealIterate_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:46:33.6132+00:00
-- url     : https://prove2.me/theorems/8ec83092-5706-4b50-b90e-c6b44e971f94
-- title:
--   Embedded Resolution: deriv Ideal Iterate add
-- statement:
--   The Embedded Resolution construction uses the deriv Ideal Iterate add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L232-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdeal.lean#L232-L237

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

theorem FunctorialResolution.EmbeddedResolution.derivIdealIterate_add (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (r s : ℕ) (J : Ideal S) :
    derivIdealIterate k (r + s) J = derivIdealIterate k r (derivIdealIterate k s J) := by sorry
