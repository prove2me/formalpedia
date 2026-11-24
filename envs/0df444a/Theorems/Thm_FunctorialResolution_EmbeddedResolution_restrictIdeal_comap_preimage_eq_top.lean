-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_comap_preimage_eq_top
-- name    : FunctorialResolution.EmbeddedResolution.restrictIdeal_comap_preimage_eq_top
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:57:44.175543+00:00
-- url     : https://prove2.me/theorems/5910311c-5bcc-468e-a302-2009a3a71de2
-- title:
--   Embedded Resolution: restrict Ideal comap preimage eq top
-- statement:
--   The Embedded Resolution construction uses the restrict Ideal comap preimage eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsChartNormalization.lean#L223-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsChartNormalization.lean#L223-L230

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization
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

theorem FunctorialResolution.EmbeddedResolution.restrictIdeal_comap_preimage_eq_top {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) (V : Y.Opens)
    (D : Y.IdealSheafData) (h : restrictIdeal D V = ⊤) :
    restrictIdeal (D.comap f) (f ⁻¹ᵁ V) = ⊤ := by sorry
