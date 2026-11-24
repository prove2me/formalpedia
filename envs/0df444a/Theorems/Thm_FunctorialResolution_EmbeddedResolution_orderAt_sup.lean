-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_sup
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_sup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:47.202829+00:00
-- url     : https://prove2.me/theorems/26de5751-0305-4ce2-a160-3e502b5ca666
-- title:
--   Embedded Resolution: order At sup
-- statement:
--   The Embedded Resolution construction uses the order At sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L203-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L203-L206

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

theorem FunctorialResolution.EmbeddedResolution.orderAt_sup (I J : X.IdealSheafData) (x : X) :
    orderAt (I ⊔ J) x = min (orderAt I x) (orderAt J x) := by sorry
