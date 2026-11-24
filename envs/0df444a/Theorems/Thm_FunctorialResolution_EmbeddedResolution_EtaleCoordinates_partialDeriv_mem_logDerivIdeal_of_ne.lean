-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDeriv_mem_logDerivIdeal_of_ne
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDeriv_mem_logDerivIdeal_of_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:57:49.695116+00:00
-- url     : https://prove2.me/theorems/4b9e68cf-03b5-4512-aa00-18490c704d96
-- title:
--   Etale Coordinates: partial Deriv mem log Deriv Ideal of ne
-- statement:
--   The Etale Coordinates construction uses the partial Deriv mem log Deriv Ideal of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/PartialDerivativeIdeal.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/PartialDerivativeIdeal.lean#L33-L37

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

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDeriv_mem_logDerivIdeal_of_ne {i h : ι} (hih : i ≠ h) (J : Ideal S) {g : S}
    (hg : g ∈ J) :
    partialDeriv k ι S i g ∈ logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J := by sorry
