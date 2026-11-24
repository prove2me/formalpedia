-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_exists_generators_maximalIdeal_of_linearIndependent_D
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_generators_maximalIdeal_of_linearIndependent_D
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:46:13.573526+00:00
-- url     : https://prove2.me/theorems/2a918395-0e30-43bd-afd2-6ec7030aebbd
-- title:
--   Etale Coordinates: exists generators maximal Ideal of linear Independent D
-- statement:
--   The Etale Coordinates construction uses the exists generators maximal Ideal of linear Independent D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/FormallyEtaleCoordinates.lean#L268-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/FormallyEtaleCoordinates.lean#L268-L326

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
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
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_generators_maximalIdeal_of_linearIndependent_D (k : Type*) [CommRing k] (S : Type*) [CommRing S] [Algebra k S]
    (q : Ideal S) [q.IsPrime] (A : Type*) [CommRing A] [Algebra S A] [Algebra k A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] (h : ℕ) (y : Fin h → A)
    (hspan : Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A)
    (hindep : LinearIndependent (IsLocalRing.ResidueField A)
      fun i : Fin h =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (y i)) :
    ∃ s : Fin h → S,
      (∀ i : Fin h, s i ∈ q) ∧
      Ideal.span (Set.range fun i : Fin h => algebraMap S A (s i)) =
        IsLocalRing.maximalIdeal A ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        fun i : Fin h =>
          (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            KaehlerDifferential.D k A (algebraMap S A (s i)) := by sorry
