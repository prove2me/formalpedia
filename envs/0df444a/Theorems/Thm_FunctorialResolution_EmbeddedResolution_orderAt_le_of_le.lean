-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_le_of_le
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_le_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:16.746915+00:00
-- url     : https://prove2.me/theorems/7c9ec6ee-d732-42f1-8785-17cb015baae4
-- title:
--   Embedded Resolution: order At le of le
-- statement:
--   The Embedded Resolution construction uses the order At le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L199-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L199-L201

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

theorem FunctorialResolution.EmbeddedResolution.orderAt_le_of_le {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    orderAt J x ≤ orderAt I x := by sorry
