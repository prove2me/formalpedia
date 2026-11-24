-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_add_orderAt_le_orderAt_mul
-- name    : FunctorialResolution.EmbeddedResolution.add_orderAt_le_orderAt_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:57.082369+00:00
-- url     : https://prove2.me/theorems/2ecaac81-8084-4242-902e-12c41c584e5d
-- title:
--   Embedded Resolution: add order At le order At mul
-- statement:
--   The Embedded Resolution construction uses the add order At le order At mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L208-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L208-L211

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

theorem FunctorialResolution.EmbeddedResolution.add_orderAt_le_orderAt_mul (I J : X.IdealSheafData) (x : X) :
    orderAt I x + orderAt J x ≤ orderAt (I * J) x := by sorry
