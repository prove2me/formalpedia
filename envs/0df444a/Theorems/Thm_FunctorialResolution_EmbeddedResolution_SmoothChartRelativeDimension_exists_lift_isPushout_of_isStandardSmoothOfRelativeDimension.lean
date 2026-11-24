-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SmoothChartRelativeDimension_exists_lift_isPushout_of_isStandardSmoothOfRelativeDimension
-- name    : FunctorialResolution.EmbeddedResolution.SmoothChartRelativeDimension.exists_lift_isPushout_of_isStandardSmoothOfRelativeDimension
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:47:49.075412+00:00
-- url     : https://prove2.me/theorems/96829c42-4f3b-4f5a-b51b-e672d51f9fc4
-- title:
--   Smooth Chart Relative Dimension: exists lift is Pushout of is Standard Smooth Of Relative Dimension
-- statement:
--   The Smooth Chart Relative Dimension construction uses the exists lift is Pushout of is Standard Smooth Of Relative Dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothAffineLiftRelativeDimension.lean#L142-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothAffineLiftRelativeDimension.lean#L142-L201

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_StandardSmoothLiftRelativeDimension
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothAffineLiftRelativeDimension
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
open scoped TensorProduct
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.SmoothChartRelativeDimension

theorem FunctorialResolution.EmbeddedResolution.SmoothChartRelativeDimension.exists_lift_isPushout_of_isStandardSmoothOfRelativeDimension {S R B : CommRingCat.{u}}
    (ι : S ⟶ R) (hι : Function.Surjective ⇑(CommRingCat.Hom.hom ι)) (φ : R ⟶ B) (r : ℕ)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom φ)) :
    ∃ (B' : CommRingCat.{u}) (σ : S ⟶ B') (ψ : B' ⟶ B),
      RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom σ) ∧
        Function.Surjective ⇑(CommRingCat.Hom.hom ψ) ∧
        CategoryTheory.IsPushout ι σ φ ψ := by sorry
