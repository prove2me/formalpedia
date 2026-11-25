-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_specMapOfFieldHom_eq
-- name    : FunctorialResolution.EmbeddedResolution.specMapOfFieldHom_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:18.603809+00:00
-- url     : https://prove2.me/theorems/3e7af965-0a57-5138-9f77-e260e738fc5d
-- title:
--   Embedded Resolution: spec Map Of Field Hom eq
-- statement:
--   The Embedded Resolution construction uses the spec Map Of Field Hom eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/FunctorialPrincipalization.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/FunctorialPrincipalization.lean#L28-L29

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ConstantCodimension
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.specMapOfFieldHom_eq (k K : Type u) [Field k] [Field K] (f : k →+* K) :
    specMapOfFieldHom k K f = Spec.map (CommRingCat.ofHom f) := by sorry
