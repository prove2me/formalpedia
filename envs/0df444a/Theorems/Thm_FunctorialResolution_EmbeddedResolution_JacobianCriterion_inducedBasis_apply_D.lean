-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_inducedBasis_apply_D
-- name    : FunctorialResolution.EmbeddedResolution.JacobianCriterion.inducedBasis_apply_D
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:35.795202+00:00
-- url     : https://prove2.me/theorems/6af5bf82-ba63-4915-85f0-baaf623991cd
-- title:
--   Jacobian Criterion: induced Basis apply D
-- statement:
--   The Jacobian Criterion construction uses the induced Basis apply D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/JacobianCriterion.lean#L304-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/JacobianCriterion.lean#L304-L307

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.JacobianCriterion
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S] [Algebra k S]
variable (S' : Type*) [CommRing S'] [Algebra k S'] [Algebra S S'] [IsScalarTower k S S']
variable [Algebra.FormallyEtale S S']

theorem FunctorialResolution.EmbeddedResolution.JacobianCriterion.inducedBasis_apply_D (b : Module.Basis ι S (KaehlerDifferential k S)) (x : ι → S)
    (hx : ∀ i : ι, b i = KaehlerDifferential.D k S (x i)) (i : ι) :
    inducedBasis k ι S S' b i = KaehlerDifferential.D k S' (algebraMap S S' (x i)) := by sorry
