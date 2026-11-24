-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationAssignment_toSequenceOfBlowups_heq_of_eq
-- name    : FunctorialResolution.EmbeddedResolution.PrincipalizationAssignment.toSequenceOfBlowups_heq_of_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:29:53.687613+00:00
-- url     : https://prove2.me/theorems/d3a0c3c9-e5dd-402a-9e7f-7003403437f7
-- title:
--   Principalization Assignment: to Sequence Of Blowups heq of eq
-- statement:
--   The Principalization Assignment construction uses the to Sequence Of Blowups heq of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/MarkedSequenceOfBlowups.lean#L188-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/MarkedSequenceOfBlowups.lean#L188-L192

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
attribute [instance] MarkedIdealWithBoundary.instField

theorem FunctorialResolution.EmbeddedResolution.PrincipalizationAssignment.toSequenceOfBlowups_heq_of_eq (L : PrincipalizationAssignment.{u})
    {T T' : MarkedIdealWithBoundary.{u}} (h : T = T') :
    HEq (L T).toSequenceOfBlowups (L T').toSequenceOfBlowups := by sorry
