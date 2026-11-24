-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_affineBlowupChart_comp_toSpec
-- name    : FunctorialResolution.Blowup.affineBlowupChart_comp_toSpec
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:39:33.886579+00:00
-- url     : https://prove2.me/theorems/bb6dbd9c-421b-41c3-b566-3bbbdd41fbf9
-- title:
--   Blowup: affine Blowup Chart comp to Spec
-- statement:
--   The Blowup construction uses the affine Blowup Chart comp to Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L136-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L136-L154

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]

theorem FunctorialResolution.Blowup.affineBlowupChart_comp_toSpec (I : Ideal R) (a : ↥I) :
    affineBlowupChart I a ≫ AffineBlowup.toSpec I =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (@algebraMap R (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) _ _
            (AffineBlowup.instAlgebraChart I a))) := by sorry
