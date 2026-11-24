-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_not_derivIdeal_le_pow
-- name    : FunctorialResolution.EmbeddedResolution.not_derivIdeal_le_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:48:58.930897+00:00
-- url     : https://prove2.me/theorems/95a15e43-90c8-4857-8027-6b57fffb165d
-- title:
--   Embedded Resolution: not deriv Ideal le pow
-- statement:
--   The Embedded Resolution construction uses the not deriv Ideal le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealOrderDecrease.lean#L151-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealOrderDecrease.lean#L151-L161

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

theorem FunctorialResolution.EmbeddedResolution.not_derivIdeal_le_pow (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) {r : ℕ} (hr : IsUnit ((r : ℕ) : R))
    {I : Ideal R} (h1 : I ≤ Ideal.span (Set.range x) ^ r)
    (h2 : ¬ I ≤ Ideal.span (Set.range x) ^ (r + 1)) :
    ¬ derivIdeal k I ≤ Ideal.span (Set.range x) ^ r := by sorry
