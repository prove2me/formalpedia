-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordSubspaceIdeal_singleton
-- name    : FunctorialResolution.EmbeddedResolution.coordSubspaceIdeal_singleton
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:37.918691+00:00
-- url     : https://prove2.me/theorems/17627b6f-b7b1-4314-921b-c369d9113f4d
-- title:
--   Embedded Resolution: coord Subspace Ideal singleton
-- statement:
--   The Embedded Resolution construction uses the coord Subspace Ideal singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean#L21-L29

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

theorem FunctorialResolution.EmbeddedResolution.coordSubspaceIdeal_singleton (k : Type u) [Field k] (m : ℕ) (j : Fin m) :
    coordSubspaceIdeal k m {j} =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)}) := by sorry
