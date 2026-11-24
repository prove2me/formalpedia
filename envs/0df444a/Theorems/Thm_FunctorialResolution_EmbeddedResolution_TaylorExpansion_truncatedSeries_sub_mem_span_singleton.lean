-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_TaylorExpansion_truncatedSeries_sub_mem_span_singleton
-- name    : FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeries_sub_mem_span_singleton
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:08.213476+00:00
-- url     : https://prove2.me/theorems/e4292edb-4e1e-46ae-af33-d67db8109a3a
-- title:
--   Taylor Expansion: truncated Series sub mem span singleton
-- statement:
--   The Taylor Expansion construction uses the truncated Series sub mem span singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansion.lean#L113-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansion.lean#L113-L125

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

theorem FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeries_sub_mem_span_singleton (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (hN : 1 ≤ N) (f : R) :
    truncatedSeries σ D β N f - σ f ∈ Ideal.span ({β} : Set S) := by sorry
