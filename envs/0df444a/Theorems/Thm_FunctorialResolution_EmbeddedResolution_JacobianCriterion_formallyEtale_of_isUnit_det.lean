-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_formallyEtale_of_isUnit_det
-- name    : FunctorialResolution.EmbeddedResolution.JacobianCriterion.formallyEtale_of_isUnit_det
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:46:03.712458+00:00
-- url     : https://prove2.me/theorems/03d05844-80e6-45d9-b7ec-2eef50769336
-- title:
--   Jacobian Criterion: formally Etale of is Unit det
-- statement:
--   The Jacobian Criterion construction uses the formally Etale of is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/JacobianCriterion.lean#L241-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/JacobianCriterion.lean#L241-L245

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
variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (S : Type*) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]

theorem FunctorialResolution.EmbeddedResolution.JacobianCriterion.formallyEtale_of_isUnit_det [Algebra.FormallySmooth k S]
    (b : Module.Basis ι S (KaehlerDifferential k S))
    (h : IsUnit (b.det fun i : ι => KaehlerDifferential.D k S (coord k ι S i))) :
    Algebra.FormallyEtale (MvPolynomial ι k) S := by sorry
