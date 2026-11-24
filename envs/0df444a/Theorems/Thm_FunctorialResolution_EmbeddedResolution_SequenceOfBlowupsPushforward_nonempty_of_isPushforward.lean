-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowupsPushforward_nonempty_of_isPushforward
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward.nonempty_of_isPushforward
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:47:22.417185+00:00
-- url     : https://prove2.me/theorems/432dddf5-16bb-4594-b26e-bbb4bfbc7e48
-- title:
--   Sequence Of Blowups Pushforward: nonempty of is Pushforward
-- statement:
--   The Sequence Of Blowups Pushforward construction uses the nonempty of is Pushforward property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/PushforwardUniqueness.lean#L76-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/PushforwardUniqueness.lean#L76-L85

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_StrictTransformClosedImmersion
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_PushforwardUniqueness
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
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward.nonempty_of_isPushforward {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B : SequenceOfBlowups X} (h : IsPushforwardBlowupSeq j BS B) :
    Nonempty (SequenceOfBlowupsPushforward j BS B) := by sorry
