-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAtGenericPoint_eq_orderAt
-- name    : FunctorialResolution.EmbeddedResolution.orderAtGenericPoint_eq_orderAt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:34.202913+00:00
-- url     : https://prove2.me/theorems/db3e22c0-44cc-58eb-9756-ea3c556761f8
-- title:
--   Embedded Resolution: order At Generic Point eq order At
-- statement:
--   The Embedded Resolution construction uses the order At Generic Point eq order At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/OrderAtGenericPoint.lean#L123-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/OrderAtGenericPoint.lean#L123-L125

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisibility
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.orderAtGenericPoint_eq_orderAt {X : Scheme.{u}} (I : X.IdealSheafData) {C : Set X}
    (hC : IsIrreducible C) :
    orderAtGenericPoint I hC = orderAt I hC.genericPoint := by sorry
