-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_blowupIsIsoOffCenter
-- name    : FunctorialResolution.Blowup.blowupIsIsoOffCenter
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:58.077129+00:00
-- url     : https://prove2.me/theorems/5e4c868d-04d5-4f37-b103-5d1ebc72ea95
-- title:
--   Blowup: blowup Is Iso Off Center
-- statement:
--   The Blowup construction uses the blowup Is Iso Off Center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupIsoOffCenter.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/BlowupIsoOffCenter.lean#L18-L22

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.Blowup

theorem FunctorialResolution.Blowup.blowupIsIsoOffCenter : BlowupIsIsoOffCenter.{u} := by sorry
