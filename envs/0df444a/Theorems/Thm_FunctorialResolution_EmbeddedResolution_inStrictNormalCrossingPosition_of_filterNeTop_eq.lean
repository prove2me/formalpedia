-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPosition_of_filterNeTop_eq
-- name    : FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_of_filterNeTop_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:59:50.106001+00:00
-- url     : https://prove2.me/theorems/824278fd-0900-52c4-a6d3-8723f911227c
-- title:
--   Embedded Resolution: in Strict Normal Crossing Position of filter Ne Top eq
-- statement:
--   The Embedded Resolution construction uses the in Strict Normal Crossing Position of filter Ne Top eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsWithoutUnitIdeals.lean#L251-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsWithoutUnitIdeals.lean#L251-L264

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

theorem FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_of_filterNeTop_eq (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] (E E' : List X.IdealSheafData)
    (h : filterNeTop E = filterNeTop E') (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition p E' := by sorry
