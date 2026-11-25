-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_strictTransform_bot_of_isBlowupAlongIdealSheaf
-- name    : FunctorialResolution.EmbeddedResolution.strictTransform_bot_of_isBlowupAlongIdealSheaf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:49:16.521241+00:00
-- url     : https://prove2.me/theorems/b8bc3e37-8181-4a1b-b37c-52d5b75c7d2b
-- title:
--   Embedded Resolution: strict Transform bot of is Blowup Along Ideal Sheaf
-- statement:
--   The Embedded Resolution construction uses the strict Transform bot of is Blowup Along Ideal Sheaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/IsoBlowupPushforward.lean#L145-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/IsoBlowupPushforward.lean#L145-L150

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

theorem FunctorialResolution.EmbeddedResolution.strictTransform_bot_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}} {π : X' ⟶ X}
    {I : X.IdealSheafData} (h : Blowup.IsBlowupAlongIdealSheaf π I) :
    Blowup.strictTransform π I (⊥ : X.IdealSheafData) = (⊥ : X'.IdealSheafData) := by sorry
