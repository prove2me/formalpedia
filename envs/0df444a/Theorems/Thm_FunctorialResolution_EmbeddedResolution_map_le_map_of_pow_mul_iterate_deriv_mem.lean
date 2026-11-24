-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_le_map_of_pow_mul_iterate_deriv_mem
-- name    : FunctorialResolution.EmbeddedResolution.map_le_map_of_pow_mul_iterate_deriv_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:52.902004+00:00
-- url     : https://prove2.me/theorems/4c889133-481a-4474-89ea-e991694bc684
-- title:
--   Embedded Resolution: map le map of pow mul iterate deriv mem
-- statement:
--   The Embedded Resolution construction uses the map le map of pow mul iterate deriv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean#L413-L444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean#L413-L444

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

theorem FunctorialResolution.EmbeddedResolution.map_le_map_of_pow_mul_iterate_deriv_mem (P : Type*) [CommRing P] {A R B : Type*}
    [CommRing A] [CommRing R] [CommRing B] [Algebra P R] [Algebra A R]
    [Algebra.FormallyUnramified P R] [IsLocalRing B] [IsNoetherianRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B) (b : R) (J : Ideal R)
    (hcong : ∀ f : R, φ f - φ' f ∈ maximalIdeal B)
    (hβ : β ∈ maximalIdeal B)
    (hrep : IsTaylorExpansionOn P φ φ' D β)
    (hb : φ b = β)
    (hstab : ∀ (j : ℕ) (g : R), g ∈ J → b ^ j * (⇑D)^[j] g ∈ J) :
    Ideal.map φ' J ≤ Ideal.map φ J := by sorry
