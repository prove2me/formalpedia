-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_monomialFactorIdeal_genericPoint
-- name    : FunctorialResolution.EmbeddedResolution.orderAt_monomialFactorIdeal_genericPoint
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:03:17.378956+00:00
-- url     : https://prove2.me/theorems/a84fbec8-1fb5-4cd6-9530-df0c963aebf6
-- title:
--   Embedded Resolution: order At monomial Factor Ideal generic Point
-- statement:
--   The Embedded Resolution construction uses the order At monomial Factor Ideal generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/MonomialPartAlongDivisor.lean#L660-L697
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MonomialCase/MonomialPartAlongDivisor.lean#L660-L697

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
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
variable {X : Scheme.{u}}
variable {k : Type u} [Field k]

theorem FunctorialResolution.EmbeddedResolution.orderAt_monomialFactorIdeal_genericPoint [TopologicalSpace.NoetherianSpace ↥X]
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (I : X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (hI : NonzeroOnComponents I) {D : X.IdealSheafData} (hD : D ∈ E) {C : Set X}
    (hC : IsIrreducibleComponentOfSupport D C) :
    orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      (orderAlongComponent I hC.isIrreducible : ℕ∞) := by sorry
