-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_chartRingHom_comp_chartSectionsIso_hom
-- name    : FunctorialResolution.Blowup.chartRingHom_comp_chartSectionsIso_hom
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:52:51.646881+00:00
-- url     : https://prove2.me/theorems/83582239-6026-4dcb-bd6a-24c41df7301d
-- title:
--   Blowup: chart Ring Hom comp chart Sections Iso hom
-- statement:
--   The Blowup construction uses the chart Ring Hom comp chart Sections Iso hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupCartier.lean#L72-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupCartier.lean#L72-L79

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
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
variable {R : Type u} [CommRing R]

theorem FunctorialResolution.Blowup.chartRingHom_comp_chartSectionsIso_hom (I : Ideal R) (a : ↥I) :
    CommRingCat.ofHom (chartRingHom I a) ≫ (chartSectionsIso I a).hom =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (AffineBlowup.toSpec I).appLE ⊤ (affineBlowupChart I a ''ᵁ ⊤)
          (le_top.trans_eq (Scheme.Hom.preimage_top (AffineBlowup.toSpec I)).symm) := by sorry
