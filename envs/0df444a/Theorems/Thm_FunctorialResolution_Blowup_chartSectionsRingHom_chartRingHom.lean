-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_chartSectionsRingHom_chartRingHom
-- name    : FunctorialResolution.Blowup.chartSectionsRingHom_chartRingHom
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:09:07.922354+00:00
-- url     : https://prove2.me/theorems/4083cfda-084d-48c2-9ac0-167cdd28e54a
-- title:
--   Blowup: chart Sections Ring Hom chart Ring Hom
-- statement:
--   The Blowup construction uses the chart Sections Ring Hom chart Ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L125-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L125-L137

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

theorem FunctorialResolution.Blowup.chartSectionsRingHom_chartRingHom {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}}
    (h : W ⟶ affineBlowup I) (b : ↥I) (V : W.Opens)
    (hV : V ≤ h ⁻¹ᵁ (affineBlowupChart I b ''ᵁ ⊤)) (r : R) :
    chartSectionsRingHom I h b V hV (chartRingHom I b r) =
      sectionsRingHom (h ≫ AffineBlowup.toSpec I) V r := by sorry
