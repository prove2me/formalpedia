-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_exceptionalDivisor_eq
-- name    : FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.exceptionalDivisor_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:29:28.019137+00:00
-- url     : https://prove2.me/theorems/a50e6104-81e6-401b-9ab4-85055cf266a0
-- title:
--   Marked Sequence Of Blowups: exceptional Divisor eq
-- statement:
--   The Marked Sequence Of Blowups construction uses the exceptional Divisor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/MarkedSequenceOfBlowups.lean#L130-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/MarkedSequenceOfBlowups.lean#L130-L131

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
open FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

theorem FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.exceptionalDivisor_eq (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.exceptionalDivisor i = (s.toSequenceOfBlowups.center i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := by sorry
