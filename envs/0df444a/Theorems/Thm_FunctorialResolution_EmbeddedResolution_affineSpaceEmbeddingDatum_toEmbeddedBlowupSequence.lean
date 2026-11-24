-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence
-- name    : FunctorialResolution.EmbeddedResolution.affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:15:09.99684+00:00
-- url     : https://prove2.me/theorems/54730c88-76e1-4bf6-a3d7-bbbca31faf1c
-- title:
--   Embedded Resolution: affine Space Embedding Datum to Embedded Blowup Sequence
-- statement:
--   The Embedded Resolution construction uses the affine Space Embedding Datum to Embedded Blowup Sequence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedBlowupSequence.lean#L447-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedBlowupSequence.lean#L447-L452

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

theorem FunctorialResolution.EmbeddedResolution.affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY] :
    (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A =
      (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence := by sorry
