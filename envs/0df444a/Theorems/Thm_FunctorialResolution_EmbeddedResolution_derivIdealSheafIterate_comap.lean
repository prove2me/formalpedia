-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_comap
-- name    : FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_comap
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:32:43.341026+00:00
-- url     : https://prove2.me/theorems/40226ef0-bece-41a2-ab7f-efb713d61067
-- title:
--   Embedded Resolution: deriv Ideal Sheaf Iterate comap
-- statement:
--   The Embedded Resolution construction uses the deriv Ideal Sheaf Iterate comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheafSmoothPullback.lean#L181-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheafSmoothPullback.lean#L181-L189

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartAlgebra
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_PolynomialCoordinateExtension
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothEtaleChart
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafSmoothPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_comap (k : Type u) [Field k] [IsNoetherianRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType (h ≫ p)] (r : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate k (h ≫ p) r (I.comap h) = (derivIdealSheafIterate k p r I).comap h := by sorry
