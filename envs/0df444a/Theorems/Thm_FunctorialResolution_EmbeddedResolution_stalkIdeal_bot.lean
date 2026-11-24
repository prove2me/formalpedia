-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_bot
-- name    : FunctorialResolution.EmbeddedResolution.stalkIdeal_bot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:49:11.656592+00:00
-- url     : https://prove2.me/theorems/d05aa479-f2d6-40f7-9c08-6d6fc7c4972c
-- title:
--   Embedded Resolution: stalk Ideal bot
-- statement:
--   The Embedded Resolution construction uses the stalk Ideal bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L86-L88

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}

theorem FunctorialResolution.EmbeddedResolution.stalkIdeal_bot (x : X) : stalkIdeal (⊥ : X.IdealSheafData) x = ⊥ := by sorry
