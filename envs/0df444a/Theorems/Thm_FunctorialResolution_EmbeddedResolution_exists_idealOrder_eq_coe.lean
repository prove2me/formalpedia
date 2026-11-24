-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_idealOrder_eq_coe
-- name    : FunctorialResolution.EmbeddedResolution.exists_idealOrder_eq_coe
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:38.967183+00:00
-- url     : https://prove2.me/theorems/e4c11fa3-d987-4682-9cde-d821cf7a468b
-- title:
--   Embedded Resolution: exists ideal Order eq coe
-- statement:
--   The Embedded Resolution construction uses the exists ideal Order eq coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L99-L102

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

theorem FunctorialResolution.EmbeddedResolution.exists_idealOrder_eq_coe [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊥) :
    ∃ n : ℕ, idealOrder I = (n : ℕ∞) := by sorry
