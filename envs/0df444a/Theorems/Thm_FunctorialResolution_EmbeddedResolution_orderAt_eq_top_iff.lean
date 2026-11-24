-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_top_iff
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_eq_top_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:49:04.156459+00:00
-- url     : https://prove2.me/theorems/104362d2-5f2c-4244-8e32-3cfec13b8b19
-- title:
--   Embedded Resolution: order At eq top iff
-- statement:
--   The Embedded Resolution construction uses the order At eq top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L241-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L241-L248

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

theorem FunctorialResolution.EmbeddedResolution.orderAt_eq_top_iff [IsLocallyNoetherian X] (I : X.IdealSheafData) (x : X) :
    orderAt I x = ⊤ ↔ stalkIdeal I x = ⊥ := by sorry
