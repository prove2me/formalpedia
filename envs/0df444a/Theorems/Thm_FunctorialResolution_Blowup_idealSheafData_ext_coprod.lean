-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_idealSheafData_ext_coprod
-- name    : FunctorialResolution.Blowup.idealSheafData_ext_coprod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:22.775415+00:00
-- url     : https://prove2.me/theorems/0926166d-acf5-54e5-bd0e-76aa3f8a3b2d
-- title:
--   Blowup: ideal Sheaf Data ext coprod
-- statement:
--   The Blowup construction uses the ideal Sheaf Data ext coprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean#L191-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean#L191-L221

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open FunctorialResolution FunctorialResolution.Blowup

theorem FunctorialResolution.Blowup.idealSheafData_ext_coprod {X Y : Scheme.{u}} (I J : (X ⨿ Y).IdealSheafData)
    (hl : I.comap (coprod.inl : X ⟶ X ⨿ Y) = J.comap (coprod.inl : X ⟶ X ⨿ Y))
    (hr : I.comap (coprod.inr : Y ⟶ X ⨿ Y) = J.comap (coprod.inr : Y ⟶ X ⨿ Y)) :
    I = J := by sorry
