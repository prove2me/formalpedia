-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
-- name    : FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:37.074612+00:00
-- url     : https://prove2.me/theorems/f4b742dd-5d34-426f-b72a-9c433cbb07cf
-- title:
--   Etale Chart: of Coords map
-- statement:
--   The Etale Chart construction uses the of Coords map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartExistence.lean#L266-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartExistence.lean#L266-L270

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) {m : ℕ}
    (v : ULift.{u} (Fin m) → U.toScheme.presheaf.obj (op ⊤))
    (he : AlgebraicGeometry.Etale (AffineSpace.homOfVector (U.ι ≫ p) v)) :
    (EtaleChart.ofCoords p U v he).map = AffineSpace.homOfVector (U.ι ≫ p) v := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
