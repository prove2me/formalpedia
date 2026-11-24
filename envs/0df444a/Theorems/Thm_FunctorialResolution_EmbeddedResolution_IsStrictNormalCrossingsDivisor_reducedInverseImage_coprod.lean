-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsStrictNormalCrossingsDivisor_reducedInverseImage_coprod
-- name    : FunctorialResolution.EmbeddedResolution.IsStrictNormalCrossingsDivisor.reducedInverseImage_coprod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:45:19.038205+00:00
-- url     : https://prove2.me/theorems/d3015a71-c369-4fde-b879-04fbeecefbfe
-- title:
--   Is Strict Normal Crossings Divisor: reduced Inverse Image coprod
-- statement:
--   The Is Strict Normal Crossings Divisor construction uses the reduced Inverse Image coprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsOpenImmersion.lean#L208-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsOpenImmersion.lean#L208-L231

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.IsStrictNormalCrossingsDivisor.reducedInverseImage_coprod {A B Z : Scheme.{u}} (g : (A ⨿ B) ⟶ Z)
    (W : TopologicalSpace.Closeds Z)
    (hA : IsStrictNormalCrossingsDivisor (reducedInverseImage ((coprod.inl : A ⟶ A ⨿ B) ≫ g) W))
    (hB : IsStrictNormalCrossingsDivisor (reducedInverseImage ((coprod.inr : B ⟶ A ⨿ B) ≫ g) W)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage g W) := by sorry
