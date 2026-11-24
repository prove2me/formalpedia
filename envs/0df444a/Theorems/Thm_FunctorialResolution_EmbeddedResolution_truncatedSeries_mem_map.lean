-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_truncatedSeries_mem_map
-- name    : FunctorialResolution.EmbeddedResolution.truncatedSeries_mem_map
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:49:07.882175+00:00
-- url     : https://prove2.me/theorems/950c43ec-e2cc-4cce-bf93-7cd103fe71f1
-- title:
--   Embedded Resolution: truncated Series mem map
-- statement:
--   The Embedded Resolution construction uses the truncated Series mem map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean#L89-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean#L89-L104

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

theorem FunctorialResolution.EmbeddedResolution.truncatedSeries_mem_map {A R B : Type*} [CommRing A] [CommRing R] [CommRing B] [Algebra A R]
    [Algebra ℚ B] (φ : R →+* B) (D : Derivation A R R) (b : R) (J : Ideal R)
    (hstab : ∀ (j : ℕ) (g : R), g ∈ J → b ^ j * (⇑D)^[j] g ∈ J)
    (N : ℕ) (g : R) (hg : g ∈ J) :
    TaylorExpansion.truncatedSeries φ D (φ b) N g ∈ Ideal.map φ J := by sorry
