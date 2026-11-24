-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_hom_ext_of_comp_eq
-- name    : FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.hom_ext_of_comp_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:15.230241+00:00
-- url     : https://prove2.me/theorems/9514ce15-6cbc-41c6-a5e1-8c39c3d08251
-- title:
--   Is Blowup Along Ideal Sheaf: hom ext of comp eq
-- statement:
--   The Is Blowup Along Ideal Sheaf construction uses the hom ext of comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupBasic.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupBasic.lean#L108-L111

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

theorem FunctorialResolution.Blowup.IsBlowupAlongIdealSheaf.hom_ext_of_comp_eq {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) {W : Scheme.{u}} {g : W ⟶ X} (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g))
    {a b : W ⟶ X'} (ha : a ≫ π = g) (hb : b ≫ π = g) : a = b := by sorry
