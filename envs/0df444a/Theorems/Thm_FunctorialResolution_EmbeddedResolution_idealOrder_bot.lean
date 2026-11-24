-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_bot
-- name    : FunctorialResolution.EmbeddedResolution.idealOrder_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:40.660356+00:00
-- url     : https://prove2.me/theorems/d9157995-f7d7-4273-b421-8717c2daef90
-- title:
--   Embedded Resolution: ideal Order bot
-- statement:
--   The Embedded Resolution construction uses the ideal Order bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealOrder.lean#L82-L85

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

theorem FunctorialResolution.EmbeddedResolution.idealOrder_bot : idealOrder (⊥ : Ideal R) = ⊤ := by sorry
