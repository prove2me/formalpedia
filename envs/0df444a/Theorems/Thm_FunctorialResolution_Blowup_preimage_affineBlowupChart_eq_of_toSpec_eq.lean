-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_preimage_affineBlowupChart_eq_of_toSpec_eq
-- name    : FunctorialResolution.Blowup.preimage_affineBlowupChart_eq_of_toSpec_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:09:36.560344+00:00
-- url     : https://prove2.me/theorems/904d744a-58d9-4424-a2c9-d49529c07232
-- title:
--   Blowup: preimage affine Blowup Chart eq of to Spec eq
-- statement:
--   The Blowup construction uses the preimage affine Blowup Chart eq of to Spec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L393-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L393-L408

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

theorem FunctorialResolution.Blowup.preimage_affineBlowupChart_eq_of_toSpec_eq {R : Type u} [CommRing R] {I : Ideal R} {W : Scheme.{u}}
    (h₁ h₂ : W ⟶ affineBlowup I)
    (he : h₁ ≫ AffineBlowup.toSpec I = h₂ ≫ AffineBlowup.toSpec I)
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h₁ ≫ AffineBlowup.toSpec I)))
    (a : ↥I) :
    h₁ ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) = h₂ ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤) := by sorry
