-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_ker_comp_coprod_inl_comap_inr
-- name    : FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:48.651519+00:00
-- url     : https://prove2.me/theorems/84f49731-0c36-4d76-a567-ec2c3ea16770
-- title:
--   Blowup: ker comp coprod inl comap inr
-- statement:
--   The Blowup construction uses the ker comp coprod inl comap inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean#L46-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean#L46-L61

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

theorem FunctorialResolution.Blowup.ker_comp_coprod_inl_comap_inr {X Y Z : Scheme.{u}} (f : Z ⟶ X)
    [QuasiCompact (f ≫ (coprod.inl : X ⟶ X ⨿ Y))] :
    (f ≫ (coprod.inl : X ⟶ X ⨿ Y)).ker.comap (coprod.inr : Y ⟶ X ⨿ Y) = ⊤ := by sorry
