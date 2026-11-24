-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordBlowupSubstMap_appTop_coord_of_mem
-- name    : FunctorialResolution.EmbeddedResolution.coordBlowupSubstMap_appTop_coord_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:54.883796+00:00
-- url     : https://prove2.me/theorems/dca23e6b-d124-4ab8-892a-125a7416d422
-- title:
--   Embedded Resolution: coord Blowup Subst Map app Top coord of mem
-- statement:
--   The Embedded Resolution construction uses the coord Blowup Subst Map app Top coord of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean#L55-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean#L55-L63

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

theorem FunctorialResolution.EmbeddedResolution.coordBlowupSubstMap_appTop_coord_of_mem (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (s : Fin m) (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s) :
    (coordBlowupSubstMap k m S s).appTop.hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j) *
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s) := by sorry
