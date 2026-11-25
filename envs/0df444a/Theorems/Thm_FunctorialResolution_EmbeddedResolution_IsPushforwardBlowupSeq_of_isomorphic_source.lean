-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsPushforwardBlowupSeq_of_isomorphic_source
-- name    : FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.of_isomorphic_source
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:55:44.379407+00:00
-- url     : https://prove2.me/theorems/94465f06-7a1a-4295-a542-5b8afa08bc46
-- title:
--   Is Pushforward Blowup Seq: of isomorphic source
-- statement:
--   The Is Pushforward Blowup Seq construction uses the of isomorphic source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/PushforwardComposition.lean#L83-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/PushforwardComposition.lean#L83-L110

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_StrictTransformClosedImmersion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_PushforwardComposition
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
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq

theorem FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.of_isomorphic_source {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    {s s' : SequenceOfBlowups S} {t : SequenceOfBlowups X}
    (hs : s.Isomorphic s') (h : IsPushforwardBlowupSeq j s t) :
    IsPushforwardBlowupSeq j s' t := by sorry
