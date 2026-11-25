-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsPullbackBlowupSequence_comp_isStrictPullbackSequenceOfBlowups
-- name    : FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence.comp_isStrictPullbackSequenceOfBlowups
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:44.567897+00:00
-- url     : https://prove2.me/theorems/e808f4de-fc2d-4ec0-954e-92bafeb184eb
-- title:
--   Is Pullback Blowup Sequence: comp is Strict Pullback Sequence Of Blowups
-- statement:
--   The Is Pullback Blowup Sequence construction uses the comp is Strict Pullback Sequence Of Blowups property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/StrictPullbackComposition.lean#L60-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/StrictPullbackComposition.lean#L60-L142

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_StrictPullbackComposition
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
open FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence

theorem FunctorialResolution.EmbeddedResolution.IsPullbackBlowupSequence.comp_isStrictPullbackSequenceOfBlowups {W V Y : Scheme.{u}} {u : V ⟶ Y} {c : W ⟶ V}
    [AlgebraicGeometry.Surjective c]
    {s : SequenceOfBlowups Y} {s' : SequenceOfBlowups V} {t : SequenceOfBlowups W}
    (h : IsPullbackBlowupSequence u s' s) (hc : IsStrictPullbackBlowupSeq c t s') :
    IsPullbackBlowupSequence (c ≫ u) t s := by sorry
