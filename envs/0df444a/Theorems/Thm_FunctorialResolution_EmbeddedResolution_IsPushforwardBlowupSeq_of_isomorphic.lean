-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsPushforwardBlowupSeq_of_isomorphic
-- name    : FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.of_isomorphic
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:39.254967+00:00
-- url     : https://prove2.me/theorems/f53a74f6-ccfa-5ff5-8061-bb40595a82e9
-- title:
--   Is Pushforward Blowup Seq: of isomorphic
-- statement:
--   The Is Pushforward Blowup Seq construction uses the of isomorphic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/IsomorphismTransport.lean#L148-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/IsomorphismTransport.lean#L148-L191

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
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

theorem FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.of_isomorphic {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (h : IsPushforwardBlowupSeq j BS B) (he : B.Isomorphic B') :
    IsPushforwardBlowupSeq j BS B' := by sorry
