-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDerivIdealIterate_one
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDerivIdealIterate_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:53:40.556867+00:00
-- url     : https://prove2.me/theorems/2b3fc536-c0c2-54aa-b9b4-14f8dc4c2621
-- title:
--   Etale Coordinates: partial Deriv Ideal Iterate one
-- statement:
--   The Etale Coordinates construction uses the partial Deriv Ideal Iterate one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/PartialDerivativeIdeal.lean#L88-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/PartialDerivativeIdeal.lean#L88-L89

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

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDerivIdealIterate_one (h : ι) (J : Ideal S) :
    partialDerivIdealIterate k ι S h 1 J = partialDerivIdeal k ι S h J := by sorry
