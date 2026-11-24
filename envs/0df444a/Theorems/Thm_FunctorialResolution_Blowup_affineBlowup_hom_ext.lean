-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_affineBlowup_hom_ext
-- name    : FunctorialResolution.Blowup.affineBlowup_hom_ext
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:09:02.390819+00:00
-- url     : https://prove2.me/theorems/dfb37024-dff1-447d-89c1-27bcbace9496
-- title:
--   Blowup: affine Blowup hom ext
-- statement:
--   The Blowup construction uses the affine Blowup hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L532-L542
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L532-L542

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

theorem FunctorialResolution.Blowup.affineBlowup_hom_ext {R : Type u} [CommRing R] {I : Ideal R} {W : Scheme.{u}}
    (h₁ h₂ : W ⟶ affineBlowup I)
    (he : h₁ ≫ AffineBlowup.toSpec I = h₂ ≫ AffineBlowup.toSpec I)
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h₁ ≫ AffineBlowup.toSpec I))) :
    h₁ = h₂ := by sorry
