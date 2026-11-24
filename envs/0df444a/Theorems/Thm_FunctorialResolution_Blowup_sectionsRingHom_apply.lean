-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_sectionsRingHom_apply
-- name    : FunctorialResolution.Blowup.sectionsRingHom_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:10:10.633802+00:00
-- url     : https://prove2.me/theorems/51e06e97-1045-422b-aeb0-bfe814d2f523
-- title:
--   Blowup: sections Ring Hom apply
-- statement:
--   The Blowup construction uses the sections Ring Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupChartPreimages.lean#L20-L24

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

theorem FunctorialResolution.Blowup.sectionsRingHom_apply {A : Type u} [CommRing A] {W : Scheme.{u}}
    (g : W ⟶ Spec (CommRingCat.of A)) (V : W.Opens) (r : A) :
    sectionsRingHom g V r =
      (g.appLE ⊤ V (le_top.trans (Scheme.Hom.preimage_top g).ge)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) := by sorry
