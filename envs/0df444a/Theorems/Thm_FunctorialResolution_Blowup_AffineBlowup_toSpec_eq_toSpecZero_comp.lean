-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_AffineBlowup_toSpec_eq_toSpecZero_comp
-- name    : FunctorialResolution.Blowup.AffineBlowup.toSpec_eq_toSpecZero_comp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:41:59.666145+00:00
-- url     : https://prove2.me/theorems/066f6319-1cfd-4e6b-9085-a86eb13daaae
-- title:
--   Affine Blowup: to Spec eq to Spec Zero comp
-- statement:
--   The Affine Blowup construction uses the to Spec eq to Spec Zero comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L36-L41

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
open FunctorialResolution.Blowup.AffineBlowup

theorem FunctorialResolution.Blowup.AffineBlowup.toSpec_eq_toSpecZero_comp (I : Ideal R) :
    toSpec I =
      AlgebraicGeometry.Proj.toSpecZero (reesGrading I) ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            ((reesDegreeZeroEquiv I : R ≃+* ↥(reesGrading I 0)) : R →+* ↥(reesGrading I 0))) := by sorry
