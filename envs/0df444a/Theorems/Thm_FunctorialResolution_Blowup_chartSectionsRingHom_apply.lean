-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_chartSectionsRingHom_apply
-- name    : FunctorialResolution.Blowup.chartSectionsRingHom_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:09:23.641813+00:00
-- url     : https://prove2.me/theorems/062fb7e1-5f61-4e8a-bb01-2c63ad4cb262
-- title:
--   Blowup: chart Sections Ring Hom apply
-- statement:
--   The Blowup construction uses the chart Sections Ring Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L117-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L117-L123

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.Blowup
universe u

theorem FunctorialResolution.Blowup.chartSectionsRingHom_apply {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}}
    (h : W ⟶ affineBlowup I) (b : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I b ''ᵁ ⊤))
    (z : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I b)) :
    chartSectionsRingHom I h b V hV z =
      (h.appLE (affineBlowupChart I b ''ᵁ ⊤) V hV).hom ((chartSectionsIso I b).hom.hom z) := by sorry
