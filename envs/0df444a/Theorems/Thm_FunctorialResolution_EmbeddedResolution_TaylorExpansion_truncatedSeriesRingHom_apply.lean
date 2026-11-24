-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_TaylorExpansion_truncatedSeriesRingHom_apply
-- name    : FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeriesRingHom_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:23.280814+00:00
-- url     : https://prove2.me/theorems/006d0b58-108c-4837-bc3f-1a727110f444
-- title:
--   Taylor Expansion: truncated Series Ring Hom apply
-- statement:
--   The Taylor Expansion construction uses the truncated Series Ring Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansion.lean#L326-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansion.lean#L326-L329

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

theorem FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeriesRingHom_apply (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (J : Ideal S)
    (hN : 1 ≤ N) (hβ : β ^ N ∈ J) (f : R) :
    truncatedSeriesRingHom σ D β N J hN hβ f = Ideal.Quotient.mk J (truncatedSeries σ D β N f) := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeriesRingHom_apply
