-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_mul_fun_add
-- name    : FunctorialResolution.EmbeddedResolution.tuningMonomial_mul_fun_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:06.614683+00:00
-- url     : https://prove2.me/theorems/2b837201-b5f0-4e16-8f13-3e1ad645c714
-- title:
--   Embedded Resolution: tuning Monomial mul fun add
-- statement:
--   The Embedded Resolution construction uses the tuning Monomial mul fun add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L61-L64

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

theorem FunctorialResolution.EmbeddedResolution.tuningMonomial_mul_fun_add (J : Ideal S) (m : ℕ) (c d : ℕ → ℕ) :
    tuningMonomial k J m c * tuningMonomial k J m d = tuningMonomial k J m (fun j => c j + d j) := by sorry
