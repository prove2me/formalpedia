-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_restrictToSubscheme_coord
-- name    : FunctorialResolution.EmbeddedResolution.EtaleChart.restrictToSubscheme_coord
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:51.667842+00:00
-- url     : https://prove2.me/theorems/1b0af81b-d6bd-4205-862f-222ec8dbacf1
-- title:
--   Etale Chart: restrict To Subscheme coord
-- statement:
--   The Etale Chart construction uses the restrict To Subscheme coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateSubscheme.lean#L519-L538
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateSubscheme.lean#L519-L538

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

theorem FunctorialResolution.EmbeddedResolution.EtaleChart.restrictToSubscheme_coord (c : EtaleChart p U m) (hU : IsAffineOpen U)
    (Z : X.IdealSheafData) (S : Finset (Fin m)) (h : restrictIdeal Z U = c.coordIdeal S)
    (i : Fin (m - S.card)) :
    (c.restrictToSubscheme hU Z S h).coord i =
      (Z.subschemeι.appLE U (Z.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord (complOrderEmb m S i)) := by sorry
