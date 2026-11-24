-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_pow_eq_tunedIdeal_mul
-- name    : FunctorialResolution.EmbeddedResolution.tunedIdeal_pow_eq_tunedIdeal_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:49:36.386338+00:00
-- url     : https://prove2.me/theorems/f64458cd-602e-471b-8fbd-d6931961e1eb
-- title:
--   Embedded Resolution: tuned Ideal pow eq tuned Ideal mul
-- statement:
--   The Embedded Resolution construction uses the tuned Ideal pow eq tuned Ideal mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdealPowers.lean#L160-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdealPowers.lean#L160-L182

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

theorem FunctorialResolution.EmbeddedResolution.tunedIdeal_pow_eq_tunedIdeal_mul (J : Ideal S) (m L : ℕ) (hL : 0 < L)
    (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L) (r : ℕ) (hr : m - 1 ≤ r) (j : ℕ) (hj : 1 ≤ j) :
    tunedIdeal k J m (r * L) ^ j = tunedIdeal k J m (j * (r * L)) := by sorry
