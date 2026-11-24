-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_mul_partialDeriv_map_eq_map_sum
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_mul_partialDeriv_map_eq_map_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:45:58.344251+00:00
-- url     : https://prove2.me/theorems/530c8044-b683-48ed-b90b-781f1a378ff4
-- title:
--   Etale Coordinates: coord mul partial Deriv map eq map sum
-- statement:
--   The Etale Coordinates construction uses the coord mul partial Deriv map eq map sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativesInBlowupCharts.lean#L117-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativesInBlowupCharts.lean#L117-L238

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativesInBlowupCharts
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
variable (k : Type*) [CommRing k] (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S₁ : Type*) [CommRing S₁] [Algebra k S₁] [Algebra (MvPolynomial ι k) S₁]
  [IsScalarTower k (MvPolynomial ι k) S₁] [Algebra.FormallyEtale (MvPolynomial ι k) S₁]
  (φ : S →ₐ[k] S₁) (T : Finset ι) (s : ι)

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_mul_partialDeriv_map_eq_map_sum
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hsT : s ∈ T) (f : S) :
    coord k ι S₁ s * partialDeriv k ι S₁ s (φ f)
      = φ (∑ i ∈ T, coord k ι S i * partialDeriv k ι S i f) := by sorry
