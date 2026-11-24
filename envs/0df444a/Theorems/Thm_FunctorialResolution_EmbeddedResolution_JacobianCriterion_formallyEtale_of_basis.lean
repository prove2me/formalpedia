-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_formallyEtale_of_basis
-- name    : FunctorialResolution.EmbeddedResolution.JacobianCriterion.formallyEtale_of_basis
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:45:32.532277+00:00
-- url     : https://prove2.me/theorems/a5c139b2-98b8-4e1b-bdae-f518f22e592d
-- title:
--   Jacobian Criterion: formally Etale of basis
-- statement:
--   The Jacobian Criterion construction uses the formally Etale of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/JacobianCriterion.lean#L183-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/JacobianCriterion.lean#L183-L203

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
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]

theorem FunctorialResolution.EmbeddedResolution.JacobianCriterion.formallyEtale_of_basis [Algebra.FormallySmooth k S]
    (b : Module.Basis ι S (KaehlerDifferential k S))
    (hb : ∀ i : ι, b i = KaehlerDifferential.D k S (coord k ι S i)) :
    Algebra.FormallyEtale (MvPolynomial ι k) S := by sorry
