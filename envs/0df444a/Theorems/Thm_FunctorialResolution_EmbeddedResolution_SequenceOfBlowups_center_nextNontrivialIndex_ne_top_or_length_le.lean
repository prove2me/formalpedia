-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_center_nextNontrivialIndex_ne_top_or_length_le
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.center_nextNontrivialIndex_ne_top_or_length_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:39:24.168813+00:00
-- url     : https://prove2.me/theorems/0d7d50eb-18cb-4b7b-b79b-dcef1685ea1f
-- title:
--   Sequence Of Blowups: center next Nontrivial Index ne top or length le
-- statement:
--   The Sequence Of Blowups construction uses the center next Nontrivial Index ne top or length le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/RemoveIsoBlowups.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/RemoveIsoBlowups.lean#L64-L66

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

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.center_nextNontrivialIndex_ne_top_or_length_le (s : SequenceOfBlowups X) (a : ℕ) :
    s.center (s.nextNontrivialIndex a) ≠ ⊤ ∨ s.length ≤ s.nextNontrivialIndex a := by sorry
