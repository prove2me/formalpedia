-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_image_subset_of_image_inter_subset
-- name    : FunctorialResolution.EmbeddedResolution.image_subset_of_image_inter_subset
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:58:49.383804+00:00
-- url     : https://prove2.me/theorems/f97de542-33b1-4c05-a506-7876f206fad7
-- title:
--   Embedded Resolution: image subset of image inter subset
-- statement:
--   The Embedded Resolution construction uses the image subset of image inter subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsChartNormalization.lean#L232-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsChartNormalization.lean#L232-L244

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

theorem FunctorialResolution.EmbeddedResolution.image_subset_of_image_inter_subset {α : Type*} {β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {A O : Set α} {g : α → β} {C : Set β} (hA : IsIrreducible A)
    (hO : IsOpen O) (hAO : (A ∩ O).Nonempty) (hg : Continuous g) (hC : IsClosed C)
    (h : g '' (A ∩ O) ⊆ C) : g '' A ⊆ C := by sorry
