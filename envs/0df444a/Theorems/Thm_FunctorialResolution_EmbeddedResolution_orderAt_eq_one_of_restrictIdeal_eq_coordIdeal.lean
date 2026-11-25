-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_one_of_restrictIdeal_eq_coordIdeal
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_eq_one_of_restrictIdeal_eq_coordIdeal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:22.806997+00:00
-- url     : https://prove2.me/theorems/84707835-1578-4447-ab66-19940d03ed98
-- title:
--   Embedded Resolution: order At eq one of restrict Ideal eq coord Ideal
-- statement:
--   The Embedded Resolution construction uses the order At eq one of restrict Ideal eq coord Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/CoordinateIdealOrderOne.lean#L106-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/CoordinateIdealOrderOne.lean#L106-L112

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorRadical
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_GermRegularParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_CoordinateIdealOrderOne
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

theorem FunctorialResolution.EmbeddedResolution.orderAt_eq_one_of_restrictIdeal_eq_coordIdeal {V : X.Opens}
    (hV : IsAffineOpen V) {n : ℕ} (c : EtaleChart p V n) (S : Finset (Fin n)) (j : Fin n)
    (hj : j ∈ S) (D : X.IdealSheafData) (hD : restrictIdeal D V = c.coordIdeal S)
    (y : X) (hy : y ∈ V) (hys : y ∈ D.support) :
    orderAt D y = 1 := by sorry
