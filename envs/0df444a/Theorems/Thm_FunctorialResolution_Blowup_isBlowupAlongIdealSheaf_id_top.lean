-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_isBlowupAlongIdealSheaf_id_top
-- name    : FunctorialResolution.Blowup.isBlowupAlongIdealSheaf_id_top
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:29.401808+00:00
-- url     : https://prove2.me/theorems/f468afc3-426a-442b-91ed-326a0ec6da12
-- title:
--   Blowup: is Blowup Along Ideal Sheaf id top
-- statement:
--   The Blowup construction uses the is Blowup Along Ideal Sheaf id top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean#L23-L24

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

theorem FunctorialResolution.Blowup.isBlowupAlongIdealSheaf_id_top (X : Scheme.{u}) : IsBlowupAlongIdealSheaf (𝟙 X) (⊤ : X.IdealSheafData) := by sorry
