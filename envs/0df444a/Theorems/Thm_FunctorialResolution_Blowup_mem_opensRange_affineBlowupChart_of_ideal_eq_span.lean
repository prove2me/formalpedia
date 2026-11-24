-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_mem_opensRange_affineBlowupChart_of_ideal_eq_span
-- name    : FunctorialResolution.Blowup.mem_opensRange_affineBlowupChart_of_ideal_eq_span
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:09:20.036494+00:00
-- url     : https://prove2.me/theorems/b48507e3-28d9-45d7-91bd-391a14dc5322
-- title:
--   Blowup: mem opens Range affine Blowup Chart of ideal eq span
-- statement:
--   The Blowup construction uses the mem opens Range affine Blowup Chart of ideal eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L298-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L298-L368

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

theorem FunctorialResolution.Blowup.mem_opensRange_affineBlowupChart_of_ideal_eq_span {R : Type u} [CommRing R]
    (I : Ideal R) {W : Scheme.{u}} (h : W ⟶ affineBlowup I)
    (hcart : IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)))
    (w : ↥W) (a : ↥I)
    (hex : ∃ V : W.affineOpens, w ∈ (V : W.Opens) ∧
      ((specIdealSheaf I).comap (h ≫ AffineBlowup.toSpec I)).ideal V =
        Ideal.span
          {sectionsRingHom (h ≫ AffineBlowup.toSpec I) (V : W.Opens) (a : R)}) :
    h.base w ∈ (affineBlowupChart I a).opensRange := by sorry
