-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_hasStrictNormalCrossingsWith_of_filterNeTop_eq
-- name    : FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_of_filterNeTop_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:48.681666+00:00
-- url     : https://prove2.me/theorems/87a6070a-43ba-5f5c-b4e8-010da2ecb038
-- title:
--   Embedded Resolution: has Strict Normal Crossings With of filter Ne Top eq
-- statement:
--   The Embedded Resolution construction uses the has Strict Normal Crossings With of filter Ne Top eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsWithoutUnitIdeals.lean#L266-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsWithoutUnitIdeals.lean#L266-L276

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

theorem FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_of_filterNeTop_eq (p : X ⟶ Spec (CommRingCat.of k))
    (Z : X.IdealSheafData) (E E' : List X.IdealSheafData)
    (h : filterNeTop E = filterNeTop E') (hE : HasStrictNormalCrossingsWith p Z E) :
    HasStrictNormalCrossingsWith p Z E' := by sorry
