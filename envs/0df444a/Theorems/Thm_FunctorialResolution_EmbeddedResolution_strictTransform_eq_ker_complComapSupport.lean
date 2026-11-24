-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_strictTransform_eq_ker_complComapSupport
-- name    : FunctorialResolution.EmbeddedResolution.strictTransform_eq_ker_complComapSupport
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:49:57.887196+00:00
-- url     : https://prove2.me/theorems/147b75a1-20be-4b7a-954f-acd16b07bf64
-- title:
--   Embedded Resolution: strict Transform eq ker compl Comap Support
-- statement:
--   The Embedded Resolution construction uses the strict Transform eq ker compl Comap Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/StrictTransformClosedImmersion.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/StrictTransformClosedImmersion.lean#L57-L65

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_StrictTransformClosedImmersion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.strictTransform_eq_ker_complComapSupport {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    Blowup.strictTransform π Z D =
      Scheme.Hom.ker
        (((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι ≫
          Scheme.Opens.ι (complComapSupport π Z)) := by sorry
