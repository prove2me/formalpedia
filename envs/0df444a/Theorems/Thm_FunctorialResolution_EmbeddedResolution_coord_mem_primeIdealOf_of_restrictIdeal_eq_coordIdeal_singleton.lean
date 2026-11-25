-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton
-- name    : FunctorialResolution.EmbeddedResolution.coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:17.046126+00:00
-- url     : https://prove2.me/theorems/2eb4d392-47c8-4de2-b091-b6fd1c791484
-- title:
--   Embedded Resolution: coord mem prime Ideal Of of restrict Ideal eq coord Ideal singleton
-- statement:
--   The Embedded Resolution construction uses the coord mem prime Ideal Of of restrict Ideal eq coord Ideal singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateDimensionBound.lean#L89-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateDimensionBound.lean#L89-L100

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_GermRegularParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateDimensionBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

theorem FunctorialResolution.EmbeddedResolution.coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton
    (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (j : Fin m) (D : X.IdealSheafData) (hD : restrictIdeal D U = c.coordIdeal {j})
    (x : X) (hx : x ∈ U) (hxD : x ∈ D.support) :
    c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by sorry
