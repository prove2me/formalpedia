-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_restrictToSubscheme_coordIdeal_singleton
-- name    : FunctorialResolution.EmbeddedResolution.EtaleChart.restrictToSubscheme_coordIdeal_singleton
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:35:25.04849+00:00
-- url     : https://prove2.me/theorems/7344c1f4-7145-4b5d-8ab6-dd7edf9beb08
-- title:
--   Etale Chart: restrict To Subscheme coord Ideal singleton
-- statement:
--   The Etale Chart construction uses the restrict To Subscheme coord Ideal singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateSubscheme.lean#L563-L602
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateSubscheme.lean#L563-L602

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
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

theorem FunctorialResolution.EmbeddedResolution.EtaleChart.restrictToSubscheme_coordIdeal_singleton (c : EtaleChart p U m)
    (hU : IsAffineOpen U) (Z : X.IdealSheafData) (S : Finset (Fin m))
    (h : restrictIdeal Z U = c.coordIdeal S) (i : Fin (m - S.card)) (E : X.IdealSheafData)
    (hE : restrictIdeal E U = c.coordIdeal {complOrderEmb m S i}) :
    restrictIdeal (E.comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U) =
      (c.restrictToSubscheme hU Z S h).coordIdeal {i} := by sorry
