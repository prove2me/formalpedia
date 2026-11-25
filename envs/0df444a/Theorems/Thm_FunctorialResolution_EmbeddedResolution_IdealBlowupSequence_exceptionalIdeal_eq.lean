-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IdealBlowupSequence_exceptionalIdeal_eq
-- name    : FunctorialResolution.EmbeddedResolution.IdealBlowupSequence.exceptionalIdeal_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:54.337806+00:00
-- url     : https://prove2.me/theorems/52b3fa4d-8728-4f60-b8ae-6dd7bb328d5f
-- title:
--   Ideal Blowup Sequence: exceptional Ideal eq
-- statement:
--   The Ideal Blowup Sequence construction uses the exceptional Ideal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/IdealBlowupSequence.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/IdealBlowupSequence.lean#L94-L95

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
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
open FunctorialResolution.EmbeddedResolution.IdealBlowupSequence
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}

theorem FunctorialResolution.EmbeddedResolution.IdealBlowupSequence.exceptionalIdeal_eq (s : IdealBlowupSequence p I E) (i : ℕ) :
    s.exceptionalIdeal i = (s.toSequenceOfBlowups.center i).comap (s.toSequenceOfBlowups.transitionMapSucc i) := by sorry
