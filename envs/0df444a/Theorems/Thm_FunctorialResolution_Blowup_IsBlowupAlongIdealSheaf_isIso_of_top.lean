-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_isIso_of_top
-- name    : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.isIso_of_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:48.206743+00:00
-- url     : https://prove2.me/theorems/9eb34814-96bd-430e-8d86-f1294bd414b1
-- title:
--   Is Blowup Along Ideal Sheaf: is Iso of top
-- statement:
--   The Is Blowup Along Ideal Sheaf construction uses the is Iso of top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupBasic.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupBasic.lean#L119-L121

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

theorem FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.isIso_of_top {X X' : Scheme.{u}} {π : X' ⟶ X}
    (h : IsBlowupAlongIdealSheaf π (⊤ : X.IdealSheafData)) : IsIso π := by sorry
