-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_mul_le
-- name    : FunctorialResolution.EmbeddedResolution.tunedIdeal_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:58.828902+00:00
-- url     : https://prove2.me/theorems/a2987155-dc57-4fce-bf30-fbcca91a2a78
-- title:
--   Embedded Resolution: tuned Ideal mul le
-- statement:
--   The Embedded Resolution construction uses the tuned Ideal mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L129-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L129-L142

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

theorem FunctorialResolution.EmbeddedResolution.tunedIdeal_mul_le (J : Ideal S) (m s t : ℕ) :
    tunedIdeal k J m s * tunedIdeal k J m t ≤ tunedIdeal k J m (s + t) := by sorry
