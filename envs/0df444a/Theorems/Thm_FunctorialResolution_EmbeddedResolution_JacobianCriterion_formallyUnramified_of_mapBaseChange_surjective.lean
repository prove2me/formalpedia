-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_formallyUnramified_of_mapBaseChange_surjective
-- name    : FunctorialResolution.EmbeddedResolution.JacobianCriterion.formallyUnramified_of_mapBaseChange_surjective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:45:54.658267+00:00
-- url     : https://prove2.me/theorems/dc014308-0abd-4402-a5f7-ebe9faebf3fa
-- title:
--   Jacobian Criterion: formally Unramified of map Base Change surjective
-- statement:
--   The Jacobian Criterion construction uses the formally Unramified of map Base Change surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/JacobianCriterion.lean#L132-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/JacobianCriterion.lean#L132-L155

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

theorem FunctorialResolution.EmbeddedResolution.JacobianCriterion.formallyUnramified_of_mapBaseChange_surjective
    (h : Function.Surjective (KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S)) :
    Algebra.FormallyUnramified (MvPolynomial ι k) S := by sorry
