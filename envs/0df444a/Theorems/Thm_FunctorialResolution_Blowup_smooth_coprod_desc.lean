-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_smooth_coprod_desc
-- name    : FunctorialResolution.Blowup.smooth_coprod_desc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:23.256794+00:00
-- url     : https://prove2.me/theorems/e4610244-48f9-4760-9543-8265010e0c5a
-- title:
--   Blowup: smooth coprod desc
-- statement:
--   The Blowup construction uses the smooth coprod desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean#L571-L583
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupCoproduct.lean#L571-L583

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

theorem FunctorialResolution.Blowup.smooth_coprod_desc {X A B : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (hf : Smooth f) (hg : Smooth g) : Smooth (coprod.desc f g) := by sorry
