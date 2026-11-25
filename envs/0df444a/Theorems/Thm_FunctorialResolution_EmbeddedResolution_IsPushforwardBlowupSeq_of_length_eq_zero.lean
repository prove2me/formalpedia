-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsPushforwardBlowupSeq_of_length_eq_zero
-- name    : FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.of_length_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:55.918831+00:00
-- url     : https://prove2.me/theorems/70b1bd8d-da7d-5d49-b6f3-3a41cf4a5299
-- title:
--   Is Pushforward Blowup Seq: of length eq zero
-- statement:
--   The Is Pushforward Blowup Seq construction uses the of length eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/IsomorphismTransport.lean#L251-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/IsomorphismTransport.lean#L251-L267

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

theorem FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.of_length_eq_zero {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X)
    (hS : BS.length = 0) (hX : B.length = 0) :
    IsPushforwardBlowupSeq j BS B := by sorry
