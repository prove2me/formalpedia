-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsStrictPullbackBlowupSeq_of_isomorphic_base
-- name    : FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.of_isomorphic_base
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:40.550219+00:00
-- url     : https://prove2.me/theorems/07bea3b9-c30e-5778-9aa9-93269d37f98b
-- title:
--   Is Strict Pullback Blowup Seq: of isomorphic base
-- statement:
--   The Is Strict Pullback Blowup Seq construction uses the of isomorphic base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PullbackBlowupSequenceComposition.lean#L154-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PullbackBlowupSequenceComposition.lean#L154-L171

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

theorem FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.of_isomorphic_base {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s s' : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (he : s.Isomorphic s') :
    IsStrictPullbackBlowupSeq g t s' := by sorry
