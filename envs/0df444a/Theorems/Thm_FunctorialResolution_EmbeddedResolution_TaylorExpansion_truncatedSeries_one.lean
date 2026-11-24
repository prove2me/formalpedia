-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_TaylorExpansion_truncatedSeries_one
-- name    : FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeries_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:47:09.735973+00:00
-- url     : https://prove2.me/theorems/10475536-5c6d-433c-875c-46856079aa77
-- title:
--   Taylor Expansion: truncated Series one
-- statement:
--   The Taylor Expansion construction uses the truncated Series one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansion.lean#L184-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansion.lean#L184-L187

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.TaylorExpansion
variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]

theorem FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeries_one (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (hN : 1 ≤ N) :
    truncatedSeries σ D β N 1 = 1 := by sorry
