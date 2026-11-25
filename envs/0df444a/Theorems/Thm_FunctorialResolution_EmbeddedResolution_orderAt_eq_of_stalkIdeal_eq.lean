-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_of_stalkIdeal_eq
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_eq_of_stalkIdeal_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:54:13.016374+00:00
-- url     : https://prove2.me/theorems/0903a560-6bf2-50e5-9d80-49473deb358c
-- title:
--   Embedded Resolution: order At eq of stalk Ideal eq
-- statement:
--   The Embedded Resolution construction uses the order At eq of stalk Ideal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L250-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L250-L252

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

theorem FunctorialResolution.EmbeddedResolution.orderAt_eq_of_stalkIdeal_eq {I J : X.IdealSheafData} {x : X}
    (h : stalkIdeal I x = stalkIdeal J x) : orderAt I x = orderAt J x := by sorry
