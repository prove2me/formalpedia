-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_isBlowupAlongIdealSheaf_affineBlowup_toSpec
-- name    : FunctorialResolution.Blowup.isBlowupAlongIdealSheaf_affineBlowup_toSpec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:25:36.041629+00:00
-- url     : https://prove2.me/theorems/4080b022-ce1e-4de2-ad51-a0274f03fcf4
-- title:
--   Blowup: is Blowup Along Ideal Sheaf affine Blowup to Spec
-- statement:
--   The Blowup construction uses the is Blowup Along Ideal Sheaf affine Blowup to Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupUniversal.lean#L195-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupUniversal.lean#L195-L203

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversalLift
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversal
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
open FunctorialResolution FunctorialResolution.Blowup
universe u

theorem FunctorialResolution.Blowup.isBlowupAlongIdealSheaf_affineBlowup_toSpec {R : Type u} [CommRing R] (I : Ideal R) :
    IsBlowupAlongIdealSheaf (AffineBlowup.toSpec I) (specIdealSheaf I) := by sorry
