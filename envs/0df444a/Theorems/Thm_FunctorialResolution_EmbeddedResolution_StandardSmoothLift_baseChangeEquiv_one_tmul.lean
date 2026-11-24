-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_StandardSmoothLift_baseChangeEquiv_one_tmul
-- name    : FunctorialResolution.EmbeddedResolution.StandardSmoothLift.baseChangeEquiv_one_tmul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:47:44.519881+00:00
-- url     : https://prove2.me/theorems/4b18632f-2387-4d6b-a262-ad5fa0dc6be8
-- title:
--   Standard Smooth Lift: base Change Equiv one tmul
-- statement:
--   The Standard Smooth Lift construction uses the base Change Equiv one tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/StandardSmoothLift.lean#L424-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/StandardSmoothLift.lean#L424-L428

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_StandardSmoothLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.StandardSmoothLift
universe u
variable {S R B : Type u} [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] {ι σ : Type} [Finite σ]
  (hsurj : Function.Surjective (algebraMap S R))
  (P : Algebra.SubmersivePresentation R B ι σ)
variable [Algebra S B] [IsScalarTower S R B]

theorem FunctorialResolution.EmbeddedResolution.StandardSmoothLift.baseChangeEquiv_one_tmul (b' : LiftedAlgebra hsurj P) :
    baseChangeEquiv hsurj P (1 ⊗ₜ[S] b') = liftedAlgebraHom hsurj P b' := by sorry
