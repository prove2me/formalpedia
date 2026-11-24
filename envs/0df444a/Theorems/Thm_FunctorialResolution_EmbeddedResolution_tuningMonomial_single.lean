-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_single
-- name    : FunctorialResolution.EmbeddedResolution.tuningMonomial_single
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:50:10.338554+00:00
-- url     : https://prove2.me/theorems/663adfe4-8821-4212-800a-81800348254d
-- title:
--   Embedded Resolution: tuning Monomial single
-- statement:
--   The Embedded Resolution construction uses the tuning Monomial single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L91-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L91-L98

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

theorem FunctorialResolution.EmbeddedResolution.tuningMonomial_single (J : Ideal S) (m i : ℕ) (hi : i ∈ Finset.range m) :
    tuningMonomial k J m (Pi.single i 1) = derivIdealIterate k i J := by sorry
