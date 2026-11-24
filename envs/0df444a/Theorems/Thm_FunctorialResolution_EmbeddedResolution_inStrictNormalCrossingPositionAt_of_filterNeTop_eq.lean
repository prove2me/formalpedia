-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPositionAt_of_filterNeTop_eq
-- name    : FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPositionAt_of_filterNeTop_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:58:48.342832+00:00
-- url     : https://prove2.me/theorems/dfef075a-980d-42a4-8736-8c6f962c6dae
-- title:
--   Embedded Resolution: in Strict Normal Crossing Position At of filter Ne Top eq
-- statement:
--   The Embedded Resolution construction uses the in Strict Normal Crossing Position At of filter Ne Top eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsWithoutUnitIdeals.lean#L242-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsWithoutUnitIdeals.lean#L242-L249

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsWithoutUnitIdeals
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k]

theorem FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPositionAt_of_filterNeTop_eq (p : X ⟶ Spec (CommRingCat.of k))
    (E E' : List X.IdealSheafData) (h : filterNeTop E = filterNeTop E') (x : X)
    (hE : InStrictNormalCrossingPositionAt p E x) : InStrictNormalCrossingPositionAt p E' x := by sorry
