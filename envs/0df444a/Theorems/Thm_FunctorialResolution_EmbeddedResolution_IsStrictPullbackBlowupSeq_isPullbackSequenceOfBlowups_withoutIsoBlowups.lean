-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsStrictPullbackBlowupSeq_isPullbackSequenceOfBlowups_withoutIsoBlowups
-- name    : FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.isPullbackSequenceOfBlowups_withoutIsoBlowups
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:54:33.287788+00:00
-- url     : https://prove2.me/theorems/8453b8d1-00d6-49c1-893f-03267cbe8515
-- title:
--   Is Strict Pullback Blowup Seq: is Pullback Sequence Of Blowups without Iso Blowups
-- statement:
--   The Is Strict Pullback Blowup Seq construction uses the is Pullback Sequence Of Blowups without Iso Blowups property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/IsoBlowupRemovalBaseChange.lean#L72-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/IsoBlowupRemovalBaseChange.lean#L72-L140

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IsoBlowupRemovalBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq

theorem FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.isPullbackSequenceOfBlowups_withoutIsoBlowups {X' X : Scheme.{u}} {φ : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq φ t s) :
    IsPullbackBlowupSequence φ t.withoutIsoBlowups s := by sorry
