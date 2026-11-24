-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDeriv_mem_sup_of_span_pow_mul_eq_map
-- name    : FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDeriv_mem_sup_of_span_pow_mul_eq_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:45:46.839798+00:00
-- url     : https://prove2.me/theorems/0cbef3b3-aed8-42d7-a7e7-8b9aad9caef0
-- title:
--   Etale Coordinates: partial Deriv mem sup of span pow mul eq map
-- statement:
--   The Etale Coordinates construction uses the partial Deriv mem sup of span pow mul eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativesInBlowupCharts.lean#L30-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativesInBlowupCharts.lean#L30-L79

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativesInBlowupCharts
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativesInBlowupCharts
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

theorem FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDeriv_mem_sup_of_span_pow_mul_eq_map
    (hin : ∀ i ∈ T, i ≠ s → φ (coord k ι S i) = coord k ι S₁ i * coord k ι S₁ s)
    (hs : φ (coord k ι S s) = coord k ι S₁ s)
    (hout : ∀ i ∉ T, φ (coord k ι S i) = coord k ι S₁ i)
    (hnzd : coord k ι S₁ s ∈ nonZeroDivisors S₁)
    (i : ι) (hiT : i ∈ T) (his : i ≠ s)
    (J : Ideal S) (L L' : Ideal S₁) (c : ℕ)
    (hJ : Ideal.span {coord k ι S₁ s ^ (c + 1)} * L = Ideal.map φ J)
    (hD : Ideal.map φ (derivIdeal k J) ≤ Ideal.span {coord k ι S₁ s ^ c} * L')
    (g : S₁) (hg : g ∈ L) :
    partialDeriv k ι S₁ i g ∈ L ⊔ L' := by sorry
