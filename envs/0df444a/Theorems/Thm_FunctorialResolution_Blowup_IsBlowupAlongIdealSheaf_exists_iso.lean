-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_exists_iso
-- name    : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.exists_iso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:11.921798+00:00
-- url     : https://prove2.me/theorems/fbfe474d-901b-42ed-b3ec-2e97b8fe66cf
-- title:
--   Is Blowup Along Ideal Sheaf: exists iso
-- statement:
--   The Is Blowup Along Ideal Sheaf construction uses the exists iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupBasic.lean#L137-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupBasic.lean#L137-L144

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open FunctorialResolution FunctorialResolution.Blowup

theorem FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.exists_iso {X X₁ X₂ : Scheme.{u}} {π₁ : X₁ ⟶ X} {π₂ : X₂ ⟶ X}
    {I : X.IdealSheafData} (h₁ : IsBlowupAlongIdealSheaf π₁ I) (h₂ : IsBlowupAlongIdealSheaf π₂ I) :
    ∃ e : X₁ ≅ X₂, e.hom ≫ π₂ = π₁ := by sorry
