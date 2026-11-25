-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_le_derivIdeal_tunedIdeal_succ
-- name    : FunctorialResolution.EmbeddedResolution.tunedIdeal_le_derivIdeal_tunedIdeal_succ
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:57.021358+00:00
-- url     : https://prove2.me/theorems/39226f52-11fb-4b54-a4ce-3e3a8673498a
-- title:
--   Embedded Resolution: tuned Ideal le deriv Ideal tuned Ideal succ
-- statement:
--   The Embedded Resolution construction uses the tuned Ideal le deriv Ideal tuned Ideal succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L458-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L458-L464

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
variable [Algebra ℚ S]

theorem FunctorialResolution.EmbeddedResolution.tunedIdeal_le_derivIdeal_tunedIdeal_succ (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S}
    (hx : x ∈ derivIdealIterate k (m - 1) J) (δ : Derivation k S S) (hδ : δ x = 1) (s : ℕ) :
    tunedIdeal k J m s ≤ derivIdeal k (tunedIdeal k J m (s + 1)) := by sorry
