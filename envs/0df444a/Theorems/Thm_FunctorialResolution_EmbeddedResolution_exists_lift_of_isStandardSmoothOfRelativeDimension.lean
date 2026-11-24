-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_lift_of_isStandardSmoothOfRelativeDimension
-- name    : FunctorialResolution.EmbeddedResolution.exists_lift_of_isStandardSmoothOfRelativeDimension
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:43.017308+00:00
-- url     : https://prove2.me/theorems/3df103cf-9070-4e7a-aa2e-bc27ab136e07
-- title:
--   Embedded Resolution: exists lift of is Standard Smooth Of Relative Dimension
-- statement:
--   The Embedded Resolution construction uses the exists lift of is Standard Smooth Of Relative Dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/StandardSmoothLiftRelativeDimension.lean#L42-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/StandardSmoothLiftRelativeDimension.lean#L42-L59

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_StandardSmoothLift
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_StandardSmoothLiftRelativeDimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (S R B : Type u) [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] [Algebra S B] [IsScalarTower S R B]

theorem FunctorialResolution.EmbeddedResolution.exists_lift_of_isStandardSmoothOfRelativeDimension (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r R B]
    (hsurj : Function.Surjective (algebraMap S R)) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra S B') (f : B' →ₐ[S] B),
      Algebra.IsStandardSmoothOfRelativeDimension r S B' ∧ Function.Surjective f ∧
        ∃ e : (R ⊗[S] B') ≃ₐ[R] B, ∀ b' : B', e (1 ⊗ₜ[S] b') = f b' := by sorry
