-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EmbeddingDatum_ambientBlowups_eq_toSequenceOfBlowups
-- name    : FunctorialResolution.EmbeddedResolution.EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:11.018207+00:00
-- url     : https://prove2.me/theorems/6e9c5440-7f39-4f32-9378-15c61561d21b
-- title:
--   Embedding Datum: ambient Blowups eq to Sequence Of Blowups
-- statement:
--   The Embedding Datum construction uses the ambient Blowups eq to Sequence Of Blowups property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedBlowupSequence.lean#L403-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/EmbeddedBlowupSequence.lean#L403-L406

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
open FunctorialResolution.EmbeddedResolution.EmbeddingDatum
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

theorem FunctorialResolution.EmbeddedResolution.EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) :
    (D.toEmbeddedBlowupSequence A).ambientSeq =
      (A k D.ambient D.ambientStruct (Scheme.Hom.ker D.emb) D.nonzeroOnComponents_ker
        ([] : List D.ambient.IdealSheafData) D.sncEmpty).toSequenceOfBlowups := by sorry
