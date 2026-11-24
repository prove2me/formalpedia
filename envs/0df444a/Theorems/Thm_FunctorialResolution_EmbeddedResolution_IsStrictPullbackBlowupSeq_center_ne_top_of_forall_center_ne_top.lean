-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsStrictPullbackBlowupSeq_center_ne_top_of_forall_center_ne_top
-- name    : FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.center_ne_top_of_forall_center_ne_top
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:45:46.983246+00:00
-- url     : https://prove2.me/theorems/1a999c05-6266-4e31-931c-854886f4a6af
-- title:
--   Is Strict Pullback Blowup Seq: center ne top of forall center ne top
-- statement:
--   The Is Strict Pullback Blowup Seq construction uses the center ne top of forall center ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PullbackBlowupSequenceComposition.lean#L228-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PullbackBlowupSequenceComposition.lean#L228-L238

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
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

theorem FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.center_ne_top_of_forall_center_ne_top {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s)
    (ht : ∀ i : ℕ, i < t.length → t.center i ≠ ⊤) :
    ∀ i : ℕ, i < s.length → s.center i ≠ ⊤ := by sorry
