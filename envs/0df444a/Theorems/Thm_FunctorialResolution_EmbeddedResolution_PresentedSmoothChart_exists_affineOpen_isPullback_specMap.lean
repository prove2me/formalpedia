-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_PresentedSmoothChart_exists_affineOpen_isPullback_specMap
-- name    : FunctorialResolution.EmbeddedResolution.PresentedSmoothChart.exists_affineOpen_isPullback_specMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:47:02.894234+00:00
-- url     : https://prove2.me/theorems/683b19d4-ddf4-4931-b7df-6b1a594ffd86
-- title:
--   Presented Smooth Chart: exists affine Open is Pullback spec Map
-- statement:
--   The Presented Smooth Chart construction uses the exists affine Open is Pullback spec Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothAffinePullbackPresentation.lean#L27-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothAffinePullbackPresentation.lean#L27-L67

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

theorem FunctorialResolution.EmbeddedResolution.PresentedSmoothChart.exists_affineOpen_isPullback_specMap {A X Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine A] [AlgebraicGeometry.IsAffine X]
    (i : X ⟶ A) [AlgebraicGeometry.IsClosedImmersion i] (r : ℕ) (h : Y ⟶ X)
    [AlgebraicGeometry.SmoothOfRelativeDimension r h] (y : ↥Y) :
    ∃ (V : Y.Opens) (_ : y ∈ V) (_ : AlgebraicGeometry.IsAffineOpen V) (B' : CommRingCat.{u})
      (σ : Γ(A, ⊤) ⟶ B') (j : (V : Scheme.{u}) ⟶ Spec B'),
      RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom σ) ∧
        AlgebraicGeometry.IsClosedImmersion j ∧
        CategoryTheory.IsPullback j (V.ι ≫ h) (Spec.map σ ≫ A.isoSpec.inv) i := by sorry
