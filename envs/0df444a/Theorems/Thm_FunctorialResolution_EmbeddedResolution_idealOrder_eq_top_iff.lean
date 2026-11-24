-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_eq_top_iff
-- name    : FunctorialResolution.EmbeddedResolution.idealOrder_eq_top_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:46.723682+00:00
-- url     : https://prove2.me/theorems/6527fc2a-0c05-47ce-9c4b-e1e6e4d0014c
-- title:
--   Embedded Resolution: ideal Order eq top iff
-- statement:
--   The Embedded Resolution construction uses the ideal Order eq top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L43-L52

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
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
variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

theorem FunctorialResolution.EmbeddedResolution.idealOrder_eq_top_iff (I : Ideal R) :
    idealOrder I = ⊤ ↔ ∀ n : ℕ, I ≤ IsLocalRing.maximalIdeal R ^ n := by sorry
