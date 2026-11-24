-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_idealOrder_iff
-- name    : FunctorialResolution.EmbeddedResolution.le_idealOrder_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:44.694671+00:00
-- url     : https://prove2.me/theorems/965d1c9e-079d-4bf6-a56c-8e7e24fa1814
-- title:
--   Embedded Resolution: le ideal Order iff
-- statement:
--   The Embedded Resolution construction uses the le ideal Order iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L12-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L12-L41

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

theorem FunctorialResolution.EmbeddedResolution.le_idealOrder_iff (I : Ideal R) (n : ℕ) :
    (n : ℕ∞) ≤ idealOrder I ↔ I ≤ IsLocalRing.maximalIdeal R ^ n := by sorry
