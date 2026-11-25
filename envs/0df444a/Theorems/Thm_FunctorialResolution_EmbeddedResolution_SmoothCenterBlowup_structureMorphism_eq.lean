-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SmoothCenterBlowup_structureMorphism_eq
-- name    : FunctorialResolution.EmbeddedResolution.SmoothCenterBlowup.structureMorphism_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:53:12.325855+00:00
-- url     : https://prove2.me/theorems/c7e4d7a4-397c-4361-b1f5-018cc78d3bd2
-- title:
--   Smooth Center Blowup: structure Morphism eq
-- statement:
--   The Smooth Center Blowup construction uses the structure Morphism eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/IdealBlowupSequence.lean#L34-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/IdealBlowupSequence.lean#L34-L34

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
open FunctorialResolution.EmbeddedResolution.SmoothCenterBlowup
variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}

theorem FunctorialResolution.EmbeddedResolution.SmoothCenterBlowup.structureMorphism_eq (s : SmoothCenterBlowup p I E) : s.structureMorphism = s.map ≫ p := by sorry
