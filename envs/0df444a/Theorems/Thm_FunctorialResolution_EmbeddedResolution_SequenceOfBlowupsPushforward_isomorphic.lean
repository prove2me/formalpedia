-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowupsPushforward_isomorphic
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward.isomorphic
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:47:25.188654+00:00
-- url     : https://prove2.me/theorems/bc96063b-6f21-499f-a821-44ea3273bb14
-- title:
--   Sequence Of Blowups Pushforward: isomorphic
-- statement:
--   The Sequence Of Blowups Pushforward construction uses the isomorphic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/PushforwardUniqueness.lean#L93-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/PushforwardUniqueness.lean#L93-L180

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

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward.isomorphic {S X : Scheme.{u}} {j : S ⟶ X} [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (d : SequenceOfBlowupsPushforward j BS B) (d' : SequenceOfBlowupsPushforward j BS B') :
    B.Isomorphic B' := by sorry
