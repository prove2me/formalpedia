-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_ideal_comap_toSpec_chart_eq_span
-- name    : FunctorialResolution.Blowup.ideal_comap_toSpec_chart_eq_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:53:29.573186+00:00
-- url     : https://prove2.me/theorems/b3f1d13e-4f5a-4432-88a9-a461e7aeddb3
-- title:
--   Blowup: ideal comap to Spec chart eq span
-- statement:
--   The Blowup construction uses the ideal comap to Spec chart eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupCartier.lean#L81-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupCartier.lean#L81-L97

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

theorem FunctorialResolution.Blowup.ideal_comap_toSpec_chart_eq_span (I : Ideal R) (a : ↥I)
    (hW : IsAffineOpen (affineBlowupChart I a ''ᵁ ⊤)) :
    ((specIdealSheaf I).comap (AffineBlowup.toSpec I)).ideal ⟨_, hW⟩ =
      Ideal.span {(chartSectionsIso I a).hom.hom (chartRingHom I a (a : R))} := by sorry
