-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddedBlowupSequence_strictTransformIdeal_succ
-- name    : FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.strictTransformIdeal_succ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:26:37.662857+00:00
-- url     : https://prove2.me/theorems/02c5422d-e7ef-4a95-b64e-ead42390360d
-- title:
--   Embedded Blowup Sequence: strict Transform Ideal succ
-- statement:
--   The Embedded Blowup Sequence construction uses the strict Transform Ideal succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedBlowupSequence.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedBlowupSequence.lean#L73-L75

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformIdeal_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.strictTransformIdeal_succ


set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
variable (T : EmbeddedBlowupSequence k Y pY)

theorem FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.strictTransformIdeal_succ (i : ℕ) :
    T.strictTransformIdeal (i + 1) =
      Blowup.strictTransform (T.blowdown i) (T.ambientCenter i) (T.strictTransformIdeal i) := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.strictTransformIdeal_succ
