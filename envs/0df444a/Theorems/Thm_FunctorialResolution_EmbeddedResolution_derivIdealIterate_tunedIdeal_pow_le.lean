-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_tunedIdeal_pow_le
-- name    : FunctorialResolution.EmbeddedResolution.derivIdealIterate_tunedIdeal_pow_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:28.727804+00:00
-- url     : https://prove2.me/theorems/84765214-20db-4173-936b-f2a5594a893b
-- title:
--   Embedded Resolution: deriv Ideal Iterate tuned Ideal pow le
-- statement:
--   The Embedded Resolution construction uses the deriv Ideal Iterate tuned Ideal pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdealPowers.lean#L184-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdealPowers.lean#L184-L196

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdealPowers
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

theorem FunctorialResolution.EmbeddedResolution.derivIdealIterate_tunedIdeal_pow_le (J : Ideal S) (m L : ℕ) (hL : 0 < L)
    (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L) (r : ℕ) (hr : m - 1 ≤ r) (i : ℕ) (hi : i < r * L) :
    derivIdealIterate k i (tunedIdeal k J m (r * L)) ^ (r * L) ≤
      tunedIdeal k J m (r * L) ^ (r * L - i) := by sorry
