-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IdealBlowupSequence_hasStrictNormalCrossingsWith_center
-- name    : FunctorialResolution.EmbeddedResolution.IdealBlowupSequence.hasStrictNormalCrossingsWith_center
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:35.479355+00:00
-- url     : https://prove2.me/theorems/1502c32a-f48b-4b9a-9419-17ef4a93b99e
-- title:
--   Ideal Blowup Sequence: has Strict Normal Crossings With center
-- statement:
--   The Ideal Blowup Sequence construction uses the has Strict Normal Crossings With center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/IdealBlowupSequence.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/IdealBlowupSequence.lean#L87-L89

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

theorem FunctorialResolution.EmbeddedResolution.IdealBlowupSequence.hasStrictNormalCrossingsWith_center (s : IdealBlowupSequence p I E) (i : ℕ) (h : i < s.toSequenceOfBlowups.length) :
    HasStrictNormalCrossingsWith (s.structureMorphism i) (s.toSequenceOfBlowups.center i) (s.boundary i) := by sorry
