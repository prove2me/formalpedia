-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsStrictPullbackBlowupSeq_comp
-- name    : FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:10.193093+00:00
-- url     : https://prove2.me/theorems/25d8edcd-424d-4038-93be-c4329e8aeecd
-- title:
--   Is Strict Pullback Blowup Seq: comp
-- statement:
--   The Is Strict Pullback Blowup Seq construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PullbackBlowupSequenceComposition.lean#L109-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/PullbackBlowupSequenceComposition.lean#L109-L123

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

theorem FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.comp {X'' X' X : Scheme.{u}} {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
    {u : SequenceOfBlowups X''} {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (hu : IsStrictPullbackBlowupSeq ψ u t) (ht : IsStrictPullbackBlowupSeq φ t s) :
    IsStrictPullbackBlowupSeq (ψ ≫ φ) u s := by sorry
