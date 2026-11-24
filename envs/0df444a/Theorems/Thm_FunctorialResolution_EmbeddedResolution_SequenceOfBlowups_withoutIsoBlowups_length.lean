-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_length
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_length
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:39:00.161922+00:00
-- url     : https://prove2.me/theorems/c2f6ad09-0d31-40d4-92ba-9a8df028685b
-- title:
--   Sequence Of Blowups: without Iso Blowups length
-- statement:
--   The Sequence Of Blowups construction uses the without Iso Blowups length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/RemoveIsoBlowups.lean#L218-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/RemoveIsoBlowups.lean#L218-L218

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
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
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
variable {X : Scheme.{u}}

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_length (s : SequenceOfBlowups X) : s.withoutIsoBlowups.length = s.lengthWithoutIsoBlowups := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_length
