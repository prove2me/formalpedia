-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_existsUnique_lift
-- name    : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.existsUnique_lift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:28.932203+00:00
-- url     : https://prove2.me/theorems/d863d1ae-8562-42f0-b96d-a7537ad308dc
-- title:
--   Is Blowup Along Ideal Sheaf: exists Unique lift
-- statement:
--   The Is Blowup Along Ideal Sheaf construction uses the exists Unique lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupBasic.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupBasic.lean#L103-L106

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

theorem FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.existsUnique_lift {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (W : Scheme.{u}) (g : W ⟶ X) (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) :
    ∃! k : W ⟶ X', k ≫ π = g := by sorry
