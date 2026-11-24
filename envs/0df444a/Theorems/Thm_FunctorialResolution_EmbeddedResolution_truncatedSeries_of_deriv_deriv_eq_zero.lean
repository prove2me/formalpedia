-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_truncatedSeries_of_deriv_deriv_eq_zero
-- name    : FunctorialResolution.EmbeddedResolution.truncatedSeries_of_deriv_deriv_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:08.636019+00:00
-- url     : https://prove2.me/theorems/b0f18b3f-e0aa-46e6-ab68-2ddc962cef75
-- title:
--   Embedded Resolution: truncated Series of deriv deriv eq zero
-- statement:
--   The Embedded Resolution construction uses the truncated Series of deriv deriv eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean#L61-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean#L61-L87

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

theorem FunctorialResolution.EmbeddedResolution.truncatedSeries_of_deriv_deriv_eq_zero (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (hN : 2 ≤ N) (f : R) (hf : D (D f) = 0) :
    TaylorExpansion.truncatedSeries σ D β N f = σ f + σ (D f) * β := by sorry
