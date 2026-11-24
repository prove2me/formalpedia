-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_projectionToBase_eq_nontrivialIndex
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_projectionToBase_eq_nontrivialIndex
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:39:49.904921+00:00
-- url     : https://prove2.me/theorems/82583c00-5866-43fd-bba6-eb1bdc956fc8
-- title:
--   Sequence Of Blowups: without Iso Blowups projection To Base eq nontrivial Index
-- statement:
--   The Sequence Of Blowups construction uses the without Iso Blowups projection To Base eq nontrivial Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/RemoveIsoBlowups.lean#L249-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/RemoveIsoBlowups.lean#L249-L253

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

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_projectionToBase_eq_nontrivialIndex (s : SequenceOfBlowups X) (j : ℕ) :
    s.withoutIsoBlowups.projectionToBase j = s.projectionToBase (s.nontrivialIndex j) := by sorry
