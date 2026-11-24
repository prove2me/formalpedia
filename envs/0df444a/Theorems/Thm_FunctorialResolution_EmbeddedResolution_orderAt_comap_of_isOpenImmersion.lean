-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_comap_of_isOpenImmersion
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:20.119555+00:00
-- url     : https://prove2.me/theorems/ee8f4113-2428-48a4-9a7d-d99a9728aabe
-- title:
--   Embedded Resolution: order At comap of is Open Immersion
-- statement:
--   The Embedded Resolution construction uses the order At comap of is Open Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L496-L536
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L496-L536

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
open CategoryTheory

theorem FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion {Y : Scheme.{u}} (h : Y ⟶ X) [IsOpenImmersion h]
    (I : X.IdealSheafData) (y : Y) :
    orderAt (I.comap h) y = orderAt I (h.base y) := by sorry
