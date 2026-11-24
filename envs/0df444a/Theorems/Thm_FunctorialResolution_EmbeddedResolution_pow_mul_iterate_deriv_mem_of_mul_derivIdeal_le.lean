-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_pow_mul_iterate_deriv_mem_of_mul_derivIdeal_le
-- name    : FunctorialResolution.EmbeddedResolution.pow_mul_iterate_deriv_mem_of_mul_derivIdeal_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:04.549194+00:00
-- url     : https://prove2.me/theorems/eee385c1-bfc9-4757-82b2-92251a6050ff
-- title:
--   Embedded Resolution: pow mul iterate deriv mem of mul deriv Ideal le
-- statement:
--   The Embedded Resolution construction uses the pow mul iterate deriv mem of mul deriv Ideal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean#L25-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/TaylorExpansionComparison.lean#L25-L49

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
variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]

theorem FunctorialResolution.EmbeddedResolution.pow_mul_iterate_deriv_mem_of_mul_derivIdeal_le (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (M J : Ideal S) (Δ : Derivation k S S) (b : S)
    (hMJ : M * derivIdeal k J ≤ J) (hb : b ∈ M) :
    ∀ (j : ℕ) (g : S), g ∈ J → b ^ j * (⇑Δ)^[j] g ∈ J := by sorry
