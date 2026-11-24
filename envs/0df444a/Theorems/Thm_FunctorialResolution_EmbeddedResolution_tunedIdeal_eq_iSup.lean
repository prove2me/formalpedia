-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_eq_iSup
-- name    : FunctorialResolution.EmbeddedResolution.tunedIdeal_eq_iSup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:11.535915+00:00
-- url     : https://prove2.me/theorems/c51bb73d-bda5-4c72-b465-45ba4f41ccfb
-- title:
--   Embedded Resolution: tuned Ideal eq i Sup
-- statement:
--   The Embedded Resolution construction uses the tuned Ideal eq i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L103-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L103-L104

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

theorem FunctorialResolution.EmbeddedResolution.tunedIdeal_eq_iSup (J : Ideal S) (m s : ℕ) :
    tunedIdeal k J m s = ⨆ c : ℕ → ℕ, ⨆ _ : s ≤ tuningWeight m c, tuningMonomial k J m c := by sorry
