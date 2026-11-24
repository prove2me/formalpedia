-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowupsPushforward_length_eq_length
-- name    : FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward.length_eq_length
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:47:16.662225+00:00
-- url     : https://prove2.me/theorems/108f593d-42cd-492b-8723-4e95d8c23d82
-- title:
--   Sequence Of Blowups Pushforward: length eq length
-- statement:
--   The Sequence Of Blowups Pushforward construction uses the length eq length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/PushforwardUniqueness.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/PushforwardUniqueness.lean#L87-L91

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

theorem FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward.length_eq_length {S X : Scheme.{u}} {j : S ⟶ X}
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (d : SequenceOfBlowupsPushforward j BS B) (d' : SequenceOfBlowupsPushforward j BS B') :
    B.length = B'.length := by sorry
