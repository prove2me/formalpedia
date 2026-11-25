-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_hom_ext_of_isBlowupAlongIdealSheaf
-- name    : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.hom_ext_of_isBlowupAlongIdealSheaf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:16.643795+00:00
-- url     : https://prove2.me/theorems/2719f5ee-6627-5b57-8ed9-1ad87f28cdb4
-- title:
--   Is Blowup Along Ideal Sheaf: hom ext of is Blowup Along Ideal Sheaf
-- statement:
--   The Is Blowup Along Ideal Sheaf construction uses the hom ext of is Blowup Along Ideal Sheaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupBasic.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupBasic.lean#L132-L135

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

theorem FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.hom_ext_of_isBlowupAlongIdealSheaf {X X₁ X₂ : Scheme.{u}} {π₁ : X₁ ⟶ X} {π₂ : X₂ ⟶ X}
    {I : X.IdealSheafData} (h₁ : IsBlowupAlongIdealSheaf π₁ I) (h₂ : IsBlowupAlongIdealSheaf π₂ I)
    {a b : X₁ ⟶ X₂} (ha : a ≫ π₂ = π₁) (hb : b ≫ π₂ = π₁) : a = b := by sorry
