-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_le_iff
-- name    : FunctorialResolution.EmbeddedResolution.tunedIdeal_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:57.966855+00:00
-- url     : https://prove2.me/theorems/3b7974c2-17b1-4273-8994-f5291bcaf21a
-- title:
--   Embedded Resolution: tuned Ideal le iff
-- statement:
--   The Embedded Resolution construction uses the tuned Ideal le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L110-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/TunedIdeal.lean#L110-L116

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

theorem FunctorialResolution.EmbeddedResolution.tunedIdeal_le_iff (J : Ideal S) (m s : ℕ) (K : Ideal S) :
    tunedIdeal k J m s ≤ K ↔ ∀ c : ℕ → ℕ, s ≤ tuningWeight m c → tuningMonomial k J m c ≤ K := by sorry
