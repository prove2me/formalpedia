-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_inducedBasis_apply
-- name    : FunctorialResolution.EmbeddedResolution.JacobianCriterion.inducedBasis_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:41.831874+00:00
-- url     : https://prove2.me/theorems/b2629a30-3f26-4bde-8678-181c19790f2d
-- title:
--   Jacobian Criterion: induced Basis apply
-- statement:
--   The Jacobian Criterion construction uses the induced Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/JacobianCriterion.lean#L299-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/JacobianCriterion.lean#L299-L302

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

theorem FunctorialResolution.EmbeddedResolution.JacobianCriterion.inducedBasis_apply (b : Module.Basis ι S (KaehlerDifferential k S)) (i : ι) :
    inducedBasis k ι S S' b i = KaehlerDifferential.map k k S S' (b i) := by sorry
