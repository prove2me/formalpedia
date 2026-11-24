-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDerivIdeal_le_iff
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDerivIdeal_le_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:58:41.624794+00:00
-- url     : https://prove2.me/theorems/1d4bf4a0-3a1d-4e8b-9818-80251405512d
-- title:
--   Etale Coordinates: partial Deriv Ideal le iff
-- statement:
--   The Etale Coordinates construction uses the partial Deriv Ideal le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/PartialDerivativeIdeal.lean#L55-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/PartialDerivativeIdeal.lean#L55-L65

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PartialDerivativeIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S]

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDerivIdeal_le_iff (h : ι) (J K : Ideal S) :
    partialDerivIdeal k ι S h J ≤ K ↔ J ≤ K ∧ ∀ g ∈ J, partialDeriv k ι S h g ∈ K := by sorry
