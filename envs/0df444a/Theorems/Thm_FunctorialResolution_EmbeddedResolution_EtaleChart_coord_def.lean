-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coord_def
-- name    : FunctorialResolution.EmbeddedResolution.EtaleChart.coord_def
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:16:47.398615+00:00
-- url     : https://prove2.me/theorems/ca924a22-6de7-4b88-825e-ce6d45f48a05
-- title:
--   Etale Chart: coord def
-- statement:
--   The Etale Chart construction uses the coord def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartRing.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartRing.lean#L48-L53

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_def

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

theorem FunctorialResolution.EmbeddedResolution.EtaleChart.coord_def (c : EtaleChart p U m) (j : Fin m) :
    c.coord j =
      U.topIso.hom.hom
        (c.map.appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))) := by sorry
