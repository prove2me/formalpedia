-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_sub_mem_iInf_span_sup_maximalIdeal_pow
-- name    : FunctorialResolution.EmbeddedResolution.sub_mem_iInf_span_sup_maximalIdeal_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:48:37.377809+00:00
-- url     : https://prove2.me/theorems/7b51cb4f-9e3f-44e4-8b1d-2be8e69c05c8
-- title:
--   Embedded Resolution: sub mem i Inf span sup maximal Ideal pow
-- statement:
--   The Embedded Resolution construction uses the sub mem i Inf span sup maximal Ideal pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean#L314-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean#L314-L330

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
open IsLocalRing

theorem FunctorialResolution.EmbeddedResolution.sub_mem_iInf_span_sup_maximalIdeal_pow (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (f : R) :
    φ f - φ' f ∈ ⨅ N : ℕ, (Ideal.span ({β} : Set B) ⊔ maximalIdeal B ^ N) := by sorry
