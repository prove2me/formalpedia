-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_center
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_center
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:38:49.988801+00:00
-- url     : https://prove2.me/theorems/580a5ea1-1b58-4118-b78a-afe2eb736c87
-- title:
--   Sequence Of Blowups: without Iso Blowups center
-- statement:
--   The Sequence Of Blowups construction uses the without Iso Blowups center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/RemoveIsoBlowups.lean#L223-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/RemoveIsoBlowups.lean#L223-L224

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

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_center (s : SequenceOfBlowups X) (j : ℕ) :
    s.withoutIsoBlowups.center j = s.center (s.nontrivialIndex j) := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_center
