-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedBlowupSequenceData_toMarkedSequence_blowupMorphism
-- name    : FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:18:03.871924+00:00
-- url     : https://prove2.me/theorems/45182ffc-fb6b-4362-82e6-b0cbd5758bc7
-- title:
--   Marked Blowup Sequence Data: to Marked Sequence blowup Morphism
-- statement:
--   The Marked Blowup Sequence Data construction uses the to Marked Sequence blowup Morphism property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/BlowupSequenceData.lean#L393-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/BlowupSequenceData.lean#L393-L395

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_BlowupSequenceData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

theorem FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism (d : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    d.toMarkedSequenceOfBlowups.toSequenceOfBlowups.transitionMapSucc i = d.toBlowupSequenceData.map i := by sorry
