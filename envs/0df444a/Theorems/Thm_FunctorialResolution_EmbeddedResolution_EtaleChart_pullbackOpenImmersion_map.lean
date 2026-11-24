-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_pullbackOpenImmersion_map
-- name    : FunctorialResolution.EmbeddedResolution.EtaleChart.pullbackOpenImmersion_map
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:57:51.109983+00:00
-- url     : https://prove2.me/theorems/91f1e191-05e5-4153-8bce-2dc61c6da6d7
-- title:
--   Etale Chart: pullback Open Immersion map
-- statement:
--   The Etale Chart construction uses the pullback Open Immersion map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsChartNormalization.lean#L205-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsChartNormalization.lean#L205-L208

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
variable {Y Y' : Scheme.{u}} {k : Type u} [Field k] {p : Y ⟶ Spec (CommRingCat.of k)}
  {V : Y.Opens} {n : ℕ}

theorem FunctorialResolution.EmbeddedResolution.EtaleChart.pullbackOpenImmersion_map (c : EtaleChart p V n) (f : Y' ⟶ Y)
    [IsOpenImmersion f] :
    (c.pullbackOpenImmersion f).map = morphismRestrict f V ≫ c.map := by sorry
