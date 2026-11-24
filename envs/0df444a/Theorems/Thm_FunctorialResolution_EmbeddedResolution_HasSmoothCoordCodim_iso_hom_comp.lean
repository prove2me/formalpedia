-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasSmoothCoordCodim_iso_hom_comp
-- name    : FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim.iso_hom_comp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:45:33.861996+00:00
-- url     : https://prove2.me/theorems/72bbe195-68f5-4a49-b32f-1093bb0b7560
-- title:
--   Has Smooth Coord Codim: iso hom comp
-- statement:
--   The Has Smooth Coord Codim construction uses the iso hom comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothCoordinateCodimensionPullback.lean#L102-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothCoordinateCodimensionPullback.lean#L102-L109

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothCoordinateCodimension
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothCoordinateCodimensionPullback
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_iso_hom_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim
variable {k : Type u} [Field k]

theorem FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim.iso_hom_comp {X X' X₀ : Scheme.{u}}
    {s : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ}
    (h : HasSmoothCoordCodim s τ c) (e : X₀ ≅ X) :
    HasSmoothCoordCodim s (e.hom ≫ τ) c := by sorry
