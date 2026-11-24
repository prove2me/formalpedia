-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_StandardSmoothLift_liftedSubmersivePresentation_dimension
-- name    : FunctorialResolution.EmbeddedResolution.StandardSmoothLift.liftedSubmersivePresentation_dimension
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:47:59.255786+00:00
-- url     : https://prove2.me/theorems/922619ea-10f5-4b3c-8a24-6784ff315173
-- title:
--   Standard Smooth Lift: lifted Submersive Presentation dimension
-- statement:
--   The Standard Smooth Lift construction uses the lifted Submersive Presentation dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/StandardSmoothLiftRelativeDimension.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/StandardSmoothLiftRelativeDimension.lean#L19-L31

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
open FunctorialResolution.EmbeddedResolution.StandardSmoothLift
variable {S R B : Type u} [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] {ι σ : Type} [Finite ι] [Finite σ]
  (hsurj : Function.Surjective (algebraMap S R))
  (P : Algebra.SubmersivePresentation R B ι σ)

theorem FunctorialResolution.EmbeddedResolution.StandardSmoothLift.liftedSubmersivePresentation_dimension :
    (liftedSubmersivePresentation hsurj P).dimension = P.dimension := by sorry
