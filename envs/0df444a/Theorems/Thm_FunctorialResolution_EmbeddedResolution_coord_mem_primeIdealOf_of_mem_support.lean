-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_coord_mem_primeIdealOf_of_mem_support
-- name    : FunctorialResolution.EmbeddedResolution.coord_mem_primeIdealOf_of_mem_support
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:57:59.726812+00:00
-- url     : https://prove2.me/theorems/7cbacc11-f890-42be-8d71-54623399aa0f
-- title:
--   Embedded Resolution: coord mem prime Ideal Of of mem support
-- statement:
--   The Embedded Resolution construction uses the coord mem prime Ideal Of of mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/OrderAtGenericPoint.lean#L151-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/OrderAtGenericPoint.lean#L151-L165

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
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))

theorem FunctorialResolution.EmbeddedResolution.coord_mem_primeIdealOf_of_mem_support {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (y : X) (hy : y ∈ V) (hys : y ∈ D.support) :
    c.coord j ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by sorry
