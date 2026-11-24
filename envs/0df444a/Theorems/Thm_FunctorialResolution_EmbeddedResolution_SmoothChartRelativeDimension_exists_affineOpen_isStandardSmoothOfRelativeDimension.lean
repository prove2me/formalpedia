-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_SmoothChartRelativeDimension_exists_affineOpen_isStandardSmoothOfRelativeDimension
-- name    : FunctorialResolution.EmbeddedResolution.SmoothChartRelativeDimension.exists_affineOpen_isStandardSmoothOfRelativeDimension
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:47:26.038823+00:00
-- url     : https://prove2.me/theorems/44270008-de33-4e83-8aff-cd94c6d28f8f
-- title:
--   Smooth Chart Relative Dimension: exists affine Open is Standard Smooth Of Relative Dimension
-- statement:
--   The Smooth Chart Relative Dimension construction uses the exists affine Open is Standard Smooth Of Relative Dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothAffineLiftRelativeDimension.lean#L35-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothAffineLiftRelativeDimension.lean#L35-L140

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

theorem FunctorialResolution.EmbeddedResolution.SmoothChartRelativeDimension.exists_affineOpen_isStandardSmoothOfRelativeDimension {X Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine X] (r : ℕ) (h : Y ⟶ X)
    [AlgebraicGeometry.SmoothOfRelativeDimension r h] (y : ↥Y) :
    ∃ (V : Y.Opens) (_ : y ∈ V) (_ : AlgebraicGeometry.IsAffineOpen V),
      RingHom.IsStandardSmoothOfRelativeDimension r
        (CommRingCat.Hom.hom ((V.ι ≫ h).appTop)) := by sorry
