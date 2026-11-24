-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_mem_detachedComponents
-- name    : FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.mem_detachedComponents
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:16:08.496932+00:00
-- url     : https://prove2.me/theorems/5cc2a705-6053-43f6-bd79-2536fd061869
-- title:
--   Embedded Blowup Sequence: mem detached Components
-- statement:
--   The Embedded Blowup Sequence construction uses the mem detached Components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedBlowupSequence.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedBlowupSequence.lean#L104-L107

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_EmbeddedResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedBlowupSequence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
variable (T : EmbeddedBlowupSequence k Y pY)

theorem FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.mem_detachedComponents (i : ℕ) (C : Set ↥(T.strictTransform i)) :
    C ∈ T.detachedComponents i ↔
      C ∈ irreducibleComponents ↥(T.strictTransform i) ∧
        (T.strictTransformι i).base '' C ⊆ ((T.ambientCenter i).support : Set ↥(T.schemeAt i)) := by sorry
