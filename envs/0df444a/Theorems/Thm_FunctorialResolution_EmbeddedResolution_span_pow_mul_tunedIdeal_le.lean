-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_span_pow_mul_tunedIdeal_le
-- name    : FunctorialResolution.EmbeddedResolution.span_pow_mul_tunedIdeal_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:48:56.924804+00:00
-- url     : https://prove2.me/theorems/d51255f9-818e-4417-a44d-d5c6c1be9fa1
-- title:
--   Embedded Resolution: span pow mul tuned Ideal le
-- statement:
--   The Embedded Resolution construction uses the span pow mul tuned Ideal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L385-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L385-L391

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

theorem FunctorialResolution.EmbeddedResolution.span_pow_mul_tunedIdeal_le (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S}
    (hx : x ∈ derivIdealIterate k (m - 1) J) (n t : ℕ) :
    Ideal.span {x ^ n} * tunedIdeal k J m t ≤ tunedIdeal k J m (t + n) := by sorry
