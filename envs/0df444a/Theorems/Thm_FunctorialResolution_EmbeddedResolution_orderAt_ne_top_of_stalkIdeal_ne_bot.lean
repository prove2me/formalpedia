-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_ne_top_of_stalkIdeal_ne_bot
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_ne_top_of_stalkIdeal_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:21.27066+00:00
-- url     : https://prove2.me/theorems/f7aa6952-3060-48e9-98d9-c4ad3fb09d86
-- title:
--   Embedded Resolution: order At ne top of stalk Ideal ne bot
-- statement:
--   The Embedded Resolution construction uses the order At ne top of stalk Ideal ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L227-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L227-L239

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

theorem FunctorialResolution.EmbeddedResolution.orderAt_ne_top_of_stalkIdeal_ne_bot [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (x : X) (h : stalkIdeal I x ≠ ⊥) : orderAt I x ≠ ⊤ := by sorry
