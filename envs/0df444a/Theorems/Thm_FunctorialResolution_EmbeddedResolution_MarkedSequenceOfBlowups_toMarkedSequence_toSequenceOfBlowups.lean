-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_toSequenceOfBlowups
-- name    : FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:29:39.229373+00:00
-- url     : https://prove2.me/theorems/06d350ea-8129-45a3-a2f1-d68fcc55701a
-- title:
--   Marked Sequence Of Blowups: to Marked Sequence to Sequence Of Blowups
-- statement:
--   The Marked Sequence Of Blowups construction uses the to Marked Sequence to Sequence Of Blowups property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/MarkedSequenceOfBlowups.lean#L255-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/MarkedSequenceOfBlowups.lean#L255-L257

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
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

theorem FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups (s : MarkedSequenceOfBlowups p I 1 E)
    (hmax : HasReducedCenters s) :
    (s.toIdealBlowupSequence hmax).toSequenceOfBlowups = s.toSequenceOfBlowups := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups
