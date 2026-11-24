-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_PresentedSmoothChart_smooth_specMap_comp_isoSpec_inv
-- name    : FunctorialResolution.EmbeddedResolution.PresentedSmoothChart.smooth_specMap_comp_isoSpec_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:48:07.894807+00:00
-- url     : https://prove2.me/theorems/a65e7021-7d30-487f-b346-3eb7be9fd416
-- title:
--   Presented Smooth Chart: smooth spec Map comp iso Spec inv
-- statement:
--   The Presented Smooth Chart construction uses the smooth spec Map comp iso Spec inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothAffinePullbackPresentation.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothAffinePullbackPresentation.lean#L13-L25

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothAffineLiftRelativeDimension
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothAffinePullbackPresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.PresentedSmoothChart

theorem FunctorialResolution.EmbeddedResolution.PresentedSmoothChart.smooth_specMap_comp_isoSpec_inv {A : Scheme.{u}} [AlgebraicGeometry.IsAffine A]
    {B' : CommRingCat.{u}} (σ : Γ(A, ⊤) ⟶ B')
    (hσ : RingHom.IsStandardSmooth (CommRingCat.Hom.hom σ)) :
    AlgebraicGeometry.Smooth (Spec.map σ ≫ A.isoSpec.inv) := by sorry
