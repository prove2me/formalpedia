-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsPushforwardBlowupSeq_of_isStrictPullback_of_isIso
-- name    : FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.of_isStrictPullback_of_isIso
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:49.906257+00:00
-- url     : https://prove2.me/theorems/f1fd3ec1-1a88-5c2c-a2dd-6732524cd307
-- title:
--   Is Pushforward Blowup Seq: of is Strict Pullback of is Iso
-- statement:
--   The Is Pushforward Blowup Seq construction uses the of is Strict Pullback of is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/IsoBlowupPushforward.lean#L152-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/IsoBlowupPushforward.lean#L152-L183

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_IsoBlowupPushforward
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.of_isStrictPullback_of_isIso {X' X : Scheme.{u}} (φ : X' ⟶ X)
    [IsIso φ] [IsClosedImmersion φ] {B' : SequenceOfBlowups X'} {B : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq φ B' B) : IsPushforwardBlowupSeq φ B' B := by sorry
