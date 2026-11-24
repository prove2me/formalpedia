-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_specIdealSheaf_ideal_top
-- name    : FunctorialResolution.Blowup.specIdealSheaf_ideal_top
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:53:18.931697+00:00
-- url     : https://prove2.me/theorems/f3767345-8937-46b7-a03d-95326c726456
-- title:
--   Blowup: spec Ideal Sheaf ideal top
-- statement:
--   The Blowup construction uses the spec Ideal Sheaf ideal top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupCartier.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupCartier.lean#L26-L29

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

theorem FunctorialResolution.Blowup.specIdealSheaf_ideal_top (I : Ideal R) :
    (specIdealSheaf I).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I := by sorry
