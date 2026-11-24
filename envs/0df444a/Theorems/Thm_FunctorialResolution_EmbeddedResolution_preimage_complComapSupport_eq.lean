-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_preimage_complComapSupport_eq
-- name    : FunctorialResolution.EmbeddedResolution.preimage_complComapSupport_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:51:50.073789+00:00
-- url     : https://prove2.me/theorems/13785e53-fd82-4fb8-86b4-68610a2bf384
-- title:
--   Embedded Resolution: preimage compl Comap Support eq
-- statement:
--   The Embedded Resolution construction uses the preimage compl Comap Support eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/StrictTransformClosedImmersion.lean#L67-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/ClosedEmbedding/StrictTransformClosedImmersion.lean#L67-L85

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

theorem FunctorialResolution.EmbeddedResolution.preimage_complComapSupport_eq {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A') [IsClosedImmersion j]
    (Z : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁)
    (hsq : j₁ ≫ π' = π ≫ j) :
    (Opens.map j₁.base).obj (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))) =
      complComapSupport π Z := by sorry
