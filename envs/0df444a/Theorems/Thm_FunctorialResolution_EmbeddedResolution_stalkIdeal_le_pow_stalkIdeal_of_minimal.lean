-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_le_pow_stalkIdeal_of_minimal
-- name    : FunctorialResolution.EmbeddedResolution.stalkIdeal_le_pow_stalkIdeal_of_minimal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:58:10.61352+00:00
-- url     : https://prove2.me/theorems/e65e5f14-c88c-4dd9-b535-5bc106de8625
-- title:
--   Embedded Resolution: stalk Ideal le pow stalk Ideal of minimal
-- statement:
--   The Embedded Resolution construction uses the stalk Ideal le pow stalk Ideal of minimal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/OrderAtGenericPoint.lean#L336-L458
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/OrderAtGenericPoint.lean#L336-L458

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

theorem FunctorialResolution.EmbeddedResolution.stalkIdeal_le_pow_stalkIdeal_of_minimal {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (x η : X) (hx : x ∈ V) (hη : η ∈ V)
    (hspec : η ⤳ x) (hηs : η ∈ D.support)
    (hmin : ∀ P : Ideal Γ(X, V), P.IsPrime → c.coord j ∈ P →
      P ≤ (hV.primeIdealOf ⟨η, hη⟩).asIdeal → P = (hV.primeIdealOf ⟨η, hη⟩).asIdeal)
    (I : X.IdealSheafData) (a : ℕ) (ha : (a : ℕ∞) ≤ orderAt I η) :
    stalkIdeal I x ≤ stalkIdeal D x ^ a := by sorry
