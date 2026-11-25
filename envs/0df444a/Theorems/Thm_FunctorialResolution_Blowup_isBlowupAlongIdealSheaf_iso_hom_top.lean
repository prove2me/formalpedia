-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_isBlowupAlongIdealSheaf_iso_hom_top
-- name    : FunctorialResolution.Blowup.isBlowupAlongIdealSheaf_iso_hom_top
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:52:53.7403+00:00
-- url     : https://prove2.me/theorems/31567be1-d554-59b1-b28b-edd460b008ce
-- title:
--   Blowup: is Blowup Along Ideal Sheaf iso hom top
-- statement:
--   The Blowup construction uses the is Blowup Along Ideal Sheaf iso hom top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean#L26-L28

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

theorem FunctorialResolution.Blowup.isBlowupAlongIdealSheaf_iso_hom_top {X X' : Scheme.{u}} (e : X' ≅ X) :
    IsBlowupAlongIdealSheaf e.hom (⊤ : X.IdealSheafData) := by sorry
