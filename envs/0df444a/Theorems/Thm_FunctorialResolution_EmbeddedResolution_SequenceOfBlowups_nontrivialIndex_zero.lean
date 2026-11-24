-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_nontrivialIndex_zero
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.nontrivialIndex_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:38:39.468888+00:00
-- url     : https://prove2.me/theorems/49cd1190-bd46-464e-b36f-1b687e0fc381
-- title:
--   Sequence Of Blowups: nontrivial Index zero
-- statement:
--   The Sequence Of Blowups construction uses the nontrivial Index zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/RemoveIsoBlowups.lean#L84-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/RemoveIsoBlowups.lean#L84-L84

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

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.nontrivialIndex_zero (s : SequenceOfBlowups X) : s.nontrivialIndex 0 = s.nextNontrivialIndex 0 := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.nontrivialIndex_zero
