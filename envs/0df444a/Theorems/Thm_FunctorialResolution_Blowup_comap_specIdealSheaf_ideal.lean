-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_comap_specIdealSheaf_ideal
-- name    : FunctorialResolution.Blowup.comap_specIdealSheaf_ideal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:08:57.269993+00:00
-- url     : https://prove2.me/theorems/6ff048fc-283a-4ea0-bdd2-424b2f85d461
-- title:
--   Blowup: comap spec Ideal Sheaf ideal
-- statement:
--   The Blowup construction uses the comap spec Ideal Sheaf ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L51-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L51-L58

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

theorem FunctorialResolution.Blowup.comap_specIdealSheaf_ideal {R : Type u} [CommRing R] (I : Ideal R) {W : Scheme.{u}}
    (g : W ⟶ Spec (CommRingCat.of R)) (V : W.affineOpens) :
    ((specIdealSheaf I).comap g).ideal V = Ideal.map (sectionsRingHom g (V : W.Opens)) I := by sorry
