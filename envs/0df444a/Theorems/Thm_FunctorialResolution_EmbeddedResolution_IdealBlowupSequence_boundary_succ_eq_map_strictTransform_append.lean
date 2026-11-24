-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IdealBlowupSequence_boundary_succ_eq_map_strictTransform_append
-- name    : FunctorialResolution.EmbeddedResolution.IdealBlowupSequence.boundary_succ_eq_map_strictTransform_append
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:45:29.57582+00:00
-- url     : https://prove2.me/theorems/3d6d8039-21fe-4841-8d5d-e848065462d4
-- title:
--   Ideal Blowup Sequence: boundary succ eq map strict Transform append
-- statement:
--   The Ideal Blowup Sequence construction uses the boundary succ eq map strict Transform append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/IdealBlowupSequence.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/IdealBlowupSequence.lean#L97-L102

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

theorem FunctorialResolution.EmbeddedResolution.IdealBlowupSequence.boundary_succ_eq_map_strictTransform_append (s : IdealBlowupSequence p I E) (i : ℕ) (h : i < s.toSequenceOfBlowups.length) :
    s.boundary (i + 1) =
      (s.boundary i).map
          (Blowup.strictTransform (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i)) ++
        [s.exceptionalIdeal i] := by sorry
