-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_tunedIdeal_le
-- name    : FunctorialResolution.EmbeddedResolution.derivIdealIterate_tunedIdeal_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:43.873799+00:00
-- url     : https://prove2.me/theorems/455b63af-8d44-44df-8318-b3246e981877
-- title:
--   Embedded Resolution: deriv Ideal Iterate tuned Ideal le
-- statement:
--   The Embedded Resolution construction uses the deriv Ideal Iterate tuned Ideal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L300-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L300-L316

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

theorem FunctorialResolution.EmbeddedResolution.derivIdealIterate_tunedIdeal_le (J : Ideal S) (m s j : ℕ) :
    derivIdealIterate k j (tunedIdeal k J m s) ≤ tunedIdeal k J m (s - j) := by sorry
