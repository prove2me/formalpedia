-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordBlowupSubstMap_appTop_coord_of_notMem
-- name    : FunctorialResolution.EmbeddedResolution.coordBlowupSubstMap_appTop_coord_of_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:19.354344+00:00
-- url     : https://prove2.me/theorems/c2c8ac6e-4d62-4f2e-b3f2-3cc62cefd307
-- title:
--   Embedded Resolution: coord Blowup Subst Map app Top coord of not Mem
-- statement:
--   The Embedded Resolution construction uses the coord Blowup Subst Map app Top coord of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean#L76-L83

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

theorem FunctorialResolution.EmbeddedResolution.coordBlowupSubstMap_appTop_coord_of_notMem (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (s : Fin m) (j : Fin m) (hj : j ∉ S) :
    (coordBlowupSubstMap k m S s).appTop.hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j) := by sorry
