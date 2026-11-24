-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_chartSectionsIso_hom_apply
-- name    : FunctorialResolution.Blowup.chartSectionsIso_hom_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:53:32.2518+00:00
-- url     : https://prove2.me/theorems/aeea62ea-858d-46cd-b0de-74f7861ce759
-- title:
--   Blowup: chart Sections Iso hom apply
-- statement:
--   The Blowup construction uses the chart Sections Iso hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupCartier.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupCartier.lean#L45-L51

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

theorem FunctorialResolution.Blowup.chartSectionsIso_hom_apply (I : Ideal R) (a : ↥I)
    (x : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) :
    (chartSectionsIso I a).hom.hom x =
      ((affineBlowupChart I a).appIso ⊤).inv.hom
        ((Scheme.ΓSpecIso
            (CommRingCat.of
              (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)))).inv.hom x) := by sorry
