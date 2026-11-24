-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_of_comap_of_isOpenImmersion_cover
-- name    : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:43.742654+00:00
-- url     : https://prove2.me/theorems/8ca808e0-b36a-4a2e-a66c-b4573f714ef6
-- title:
--   Is Blowup Along Ideal Sheaf: of comap of is Open Immersion cover
-- statement:
--   The Is Blowup Along Ideal Sheaf construction uses the of comap of is Open Immersion cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupOpenCover.lean#L214-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupOpenCover.lean#L214-L271

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open FunctorialResolution FunctorialResolution.Blowup

theorem FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover {X X' : Scheme.{u}} (π : X' ⟶ X)
    (I : X.IdealSheafData) {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base)
    (h : ∀ i, IsBlowupAlongIdealSheaf (pullback.snd π (f i)) (I.comap (f i))) :
    IsBlowupAlongIdealSheaf π I := by sorry
