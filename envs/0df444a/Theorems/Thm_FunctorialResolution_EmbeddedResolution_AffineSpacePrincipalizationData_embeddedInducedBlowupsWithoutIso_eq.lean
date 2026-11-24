-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_embeddedInducedBlowupsWithoutIso_eq
-- name    : FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.embeddedInducedBlowupsWithoutIso_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:15:14.929078+00:00
-- url     : https://prove2.me/theorems/f0f0164b-1619-4f6b-9d50-2779f8a7c51b
-- title:
--   Affine Space Principalization Data: embedded Induced Blowups Without Iso eq
-- statement:
--   The Affine Space Principalization Data construction uses the embedded Induced Blowups Without Iso eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedBlowupSequence.lean#L370-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedBlowupSequence.lean#L370-L374

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
open FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

theorem FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.embeddedInducedBlowupsWithoutIso_eq (S : AffineSpacePrincipalizationData k Y pY) (h : S.TransitionsAreBlowups) :
    S.toEmbeddedBlowupSequence.inducedBlowupsWithoutIso ((toEmbeddedBlowupSequence_transitionsAreBlowups_iff S).mpr h) = S.blowupSequenceWithoutIsos h := by sorry
