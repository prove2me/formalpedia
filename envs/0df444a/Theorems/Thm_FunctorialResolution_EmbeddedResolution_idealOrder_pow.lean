-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_pow
-- name    : FunctorialResolution.EmbeddedResolution.idealOrder_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:48:03.218706+00:00
-- url     : https://prove2.me/theorems/b402ec7a-af33-4ed6-8874-881e8f325537
-- title:
--   Embedded Resolution: ideal Order pow
-- statement:
--   The Embedded Resolution construction uses the ideal Order pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LeadingForm.lean#L335-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LeadingForm.lean#L335-L348

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LeadingForm
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

theorem FunctorialResolution.EmbeddedResolution.idealOrder_pow {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a))
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R)) (I : Ideal R) (c : ℕ) :
    idealOrder (I ^ c) = (c : ℕ∞) * idealOrder I := by sorry
