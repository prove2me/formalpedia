-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_derivIdeal_of_isUnit_natCast
-- name    : FunctorialResolution.EmbeddedResolution.idealOrder_derivIdeal_of_isUnit_natCast
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:47:47.970935+00:00
-- url     : https://prove2.me/theorems/d9c9f133-a33e-498c-80b5-3de7e0312b54
-- title:
--   Embedded Resolution: ideal Order deriv Ideal of is Unit nat Cast
-- statement:
--   The Embedded Resolution construction uses the ideal Order deriv Ideal of is Unit nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealOrderDecrease.lean#L175-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealOrderDecrease.lean#L175-L203

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
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

theorem FunctorialResolution.EmbeddedResolution.idealOrder_derivIdeal_of_isUnit_natCast (k : Type*) [CommRing k] {R : Type*} [CommRing R] [IsLocalRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
    {I : Ideal R} {r : ℕ} (hr : 1 ≤ r) (hI : idealOrder I = (r : ℕ∞)) :
    idealOrder (derivIdeal k I) = ((r - 1 : ℕ) : ℕ∞) := by sorry
