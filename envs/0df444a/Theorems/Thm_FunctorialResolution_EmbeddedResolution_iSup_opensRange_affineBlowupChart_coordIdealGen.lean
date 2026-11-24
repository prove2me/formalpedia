-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_iSup_opensRange_affineBlowupChart_coordIdealGen
-- name    : FunctorialResolution.EmbeddedResolution.iSup_opensRange_affineBlowupChart_coordIdealGen
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:17.993716+00:00
-- url     : https://prove2.me/theorems/ab7b6a28-5132-40ab-a076-99834d6acc68
-- title:
--   Embedded Resolution: i Sup opens Range affine Blowup Chart coord Ideal Gen
-- statement:
--   The Embedded Resolution construction uses the i Sup opens Range affine Blowup Chart coord Ideal Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateBlowupChart.lean#L69-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateBlowupChart.lean#L69-L91

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversalLift
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateBlowupChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u v

theorem FunctorialResolution.EmbeddedResolution.iSup_opensRange_affineBlowupChart_coordIdealGen (R : Type u) [CommRing R] {σ : Type v}
    (S : Finset σ) :
    (⨆ i : ↥S, Scheme.Hom.opensRange
        (Blowup.affineBlowupChart (coordIdeal R S) (coordIdealGen R S i.1 i.2)))
      = (⊤ : (Blowup.affineBlowup (coordIdeal R S)).Opens) := by sorry
