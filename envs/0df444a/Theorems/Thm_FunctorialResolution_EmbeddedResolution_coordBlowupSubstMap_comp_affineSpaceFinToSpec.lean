-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordBlowupSubstMap_comp_affineSpaceFinToSpec
-- name    : FunctorialResolution.EmbeddedResolution.coordBlowupSubstMap_comp_affineSpaceFinToSpec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:41.318356+00:00
-- url     : https://prove2.me/theorems/808f9131-9915-45fd-ae98-ac94c1971363
-- title:
--   Embedded Resolution: coord Blowup Subst Map comp affine Space Fin To Spec
-- statement:
--   The Embedded Resolution construction uses the coord Blowup Subst Map comp affine Space Fin To Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean#L41-L43

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.coordBlowupSubstMap_comp_affineSpaceFinToSpec (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) :
    coordBlowupSubstMap k m S s ≫ affineSpaceFinToSpec k m = affineSpaceFinToSpec k m := by sorry
