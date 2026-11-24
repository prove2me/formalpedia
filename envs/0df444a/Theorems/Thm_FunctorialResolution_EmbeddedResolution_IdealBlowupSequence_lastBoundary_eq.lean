-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IdealBlowupSequence_lastBoundary_eq
-- name    : FunctorialResolution.EmbeddedResolution.IdealBlowupSequence.lastBoundary_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:44:57.790807+00:00
-- url     : https://prove2.me/theorems/b81ca7a6-5b6e-4b55-8d02-58fbc2e96f9f
-- title:
--   Ideal Blowup Sequence: last Boundary eq
-- statement:
--   The Ideal Blowup Sequence construction uses the last Boundary eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/IdealBlowupSequence.lean#L115-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/IdealBlowupSequence.lean#L115-L116

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

theorem FunctorialResolution.EmbeddedResolution.IdealBlowupSequence.lastBoundary_eq (s : IdealBlowupSequence p I E) :
    s.lastBoundary = s.boundary s.toSequenceOfBlowups.length := by sorry
