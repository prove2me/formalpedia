-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst
-- name    : FunctorialResolution.EmbeddedResolution.awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:01:28.9648+00:00
-- url     : https://prove2.me/theorems/a706c1f2-8503-48c6-b0df-dc26e1868db7
-- title:
--   Embedded Resolution: away Coord Gen Equiv Mv Polynomial symm comp coord Blowup Subst
-- statement:
--   The Embedded Resolution construction uses the away Coord Gen Equiv Mv Polynomial symm comp coord Blowup Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateBlowupChart.lean#L388-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateBlowupChart.lean#L388-L392

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversalLift
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateBlowupChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u v

theorem FunctorialResolution.EmbeddedResolution.awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    (awayCoordGenEquivMvPolynomial R S s hs).symm.toRingHom.comp (coordBlowupSubst R S s).toRingHom
      = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) := by sorry
