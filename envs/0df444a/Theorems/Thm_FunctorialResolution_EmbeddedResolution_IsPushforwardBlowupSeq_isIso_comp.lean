-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsPushforwardBlowupSeq_isIso_comp
-- name    : FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.isIso_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:45:09.869688+00:00
-- url     : https://prove2.me/theorems/e3360465-ad8d-4c5d-b4af-b1fafb6815bf
-- title:
--   Is Pushforward Blowup Seq: is Iso comp
-- statement:
--   The Is Pushforward Blowup Seq construction uses the is Iso comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/IsomorphismTransport.lean#L193-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/IsomorphismTransport.lean#L193-L249

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

theorem FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.isIso_comp {S' S X : Scheme.{u}} (e : S' ⟶ S) [IsIso e]
    (j : S ⟶ X) [IsClosedImmersion j] (j' : S' ⟶ X) [IsClosedImmersion j']
    (hj : j' = e ≫ j)
    {BS' : SequenceOfBlowups S'} {BS : SequenceOfBlowups S} {B : SequenceOfBlowups X}
    (hpb : IsStrictPullbackBlowupSeq e BS' BS) (h : IsPushforwardBlowupSeq j BS B) :
    IsPushforwardBlowupSeq j' BS' B := by sorry
