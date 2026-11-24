-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_comap_specIdealSheaf_ideal_eq_span
-- name    : FunctorialResolution.Blowup.comap_specIdealSheaf_ideal_eq_span
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:08:45.44773+00:00
-- url     : https://prove2.me/theorems/88eb29ed-5307-49d9-92a2-3cb0a8763183
-- title:
--   Blowup: comap spec Ideal Sheaf ideal eq span
-- statement:
--   The Blowup construction uses the comap spec Ideal Sheaf ideal eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L139-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L139-L154

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

theorem FunctorialResolution.Blowup.comap_specIdealSheaf_ideal_eq_span {R : Type u} [CommRing R] (I : Ideal R)
    {W : Scheme.{u}} (h : W ⟶ affineBlowup I) (a : ↥I) (V : W.affineOpens)
    (hV : (V : W.Opens) ≤ h ⁻¹ᵁ (affineBlowupChart I a ''ᵁ ⊤)) :
    ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal V =
      Ideal.span
        {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R)} := by sorry
