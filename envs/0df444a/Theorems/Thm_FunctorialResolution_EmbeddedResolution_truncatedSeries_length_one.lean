-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_truncatedSeries_length_one
-- name    : FunctorialResolution.EmbeddedResolution.truncatedSeries_length_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:03.389087+00:00
-- url     : https://prove2.me/theorems/af1fee98-abe0-44c4-865d-ddb5ea663f52
-- title:
--   Embedded Resolution: truncated Series length one
-- statement:
--   The Embedded Resolution construction uses the truncated Series length one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean#L57-L59

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]

theorem FunctorialResolution.EmbeddedResolution.truncatedSeries_length_one (σ : R →+* S) (D : Derivation A R R) (β : S) (f : R) :
    TaylorExpansion.truncatedSeries σ D β 1 f = σ f := by sorry
