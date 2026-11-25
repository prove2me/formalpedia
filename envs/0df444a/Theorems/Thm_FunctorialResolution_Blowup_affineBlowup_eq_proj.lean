-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_affineBlowup_eq_proj
-- name    : FunctorialResolution.Blowup.affineBlowup_eq_proj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:35.183301+00:00
-- url     : https://prove2.me/theorems/c362d75e-2afa-4298-9b8c-949e7df3f712
-- title:
--   Blowup: affine Blowup eq proj
-- statement:
--   The Blowup construction uses the affine Blowup eq proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L24-L25

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

theorem FunctorialResolution.Blowup.affineBlowup_eq_proj (I : Ideal R) :
    affineBlowup I = AlgebraicGeometry.Proj (reesGrading I) := by sorry
